/***********************************************************************
Copyright (c) 2014-2018, Jan Elffers

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
***********************************************************************/

using namespace std;
#include <vector>
#include <iostream>
#include <sstream>
#include <fstream>
#include <cmath>
#include <algorithm>
#include <cstdio>
#include <cassert>
#include <cstring>
#include <csignal>
#include <map>
#include <set>

#include <getopt.h>

void exit_SAT(),exit_UNSAT(),exit_INDETERMINATE();

// Minisat cpuTime function
#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>
static inline double cpuTime(void) {
	struct rusage ru;
	getrusage(RUSAGE_SELF, &ru);
	return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000; }

struct Clause {
	struct {
		unsigned markedfordel : 1;
		unsigned learnt       : 1;
		unsigned size         : 30; } header;
	// watch data
	int nwatch;
	// ordinary data
	int w;
	int mxcoef;
	float act;
	int lbd;
	int data[0];

	size_t size() const { return header.size; }
	
	int * lits() { return data; }
	int * coefs() { return (int*)(data+header.size); }
	
	bool learnt() const { return header.learnt; }
	bool markedfordel() const { return header.markedfordel; }
	void markfordel() { header.markedfordel=1; }
};
struct lit{int l;lit(int l):l(l){}};
ostream&operator<<(ostream&o,lit const&l){if(l.l<0)o<<"~";o<<"x"<<abs(l.l);return o;}
ostream & operator<<(ostream & o, Clause & C) {
	map<int,int> M;for(size_t i=0;i<C.size();i++)M[C.lits()[i]]=C.coefs()[i];
	int i=0;
	for(auto p:M){
		int l=p.first;
		int coef=p.second;
		if(i!=0)o<<" + ";
		if(coef!=1)o<<coef<<" ";
		o<<lit(l);
		i++;
	}
	o<<" >= "<<C.w;
	o<<" (#watches="<<C.nwatch<<")";
	return o;
}

// ---------------------------------------------------------------------
// memory. maximum supported size of learnt clause database is 16GB
struct CRef {
	uint32_t ofs;
	bool operator==(CRef const&o)const{return ofs==o.ofs;}
	bool operator!=(CRef const&o)const{return ofs!=o.ofs;}
	bool operator< (CRef const&o)const{return ofs< o.ofs;}
};
const CRef CRef_Undef = { UINT32_MAX };

class OutOfMemoryException{};
static inline void* xrealloc(void *ptr, size_t size)
{
	void* mem = realloc(ptr, size);
	if (mem == NULL && errno == ENOMEM){
		throw OutOfMemoryException();
	}else
		return mem;
}
struct {
	uint32_t* memory;
	uint32_t at, cap;
	uint32_t wasted; // for GC
	void capacity(uint32_t min_cap)
	{
		if (cap >= min_cap) return;

		uint32_t prev_cap = cap;
		while (cap < min_cap){
			// NOTE: Multiply by a factor (13/8) without causing overflow, then add 2 and make the
			// result even by clearing the least significant bit. The resulting sequence of capacities
			// is carefully chosen to hit a maximum capacity that is close to the '2^32-1' limit when
			// using 'uint32_t' as indices so that as much as possible of this space can be used.
			uint32_t delta = ((cap >> 1) + (cap >> 3) + 2) & ~1;
			cap += delta;

			if (cap <= prev_cap)
				throw OutOfMemoryException();
		}
		// printf(" .. (%p) cap = %u\n", this, cap);

		assert(cap > 0);
		memory = (uint32_t*) xrealloc(memory, sizeof(uint32_t) * cap);
	}
	int sz_clause(int length) { return (sizeof(Clause)+sizeof(int)*length+sizeof(int)*length)/sizeof(uint32_t); }
	CRef alloc(vector<int> lits, vector<int> coefs, int w, bool learnt){
		assert(!lits.empty());
		int length = (int) lits.size();
		// note: coefficients can be arbitrarily ordered (we don't sort them in descending order for example)
		// during maintenance of watches the order will be shuffled.
		capacity(at + sz_clause(length));
		Clause * clause = (Clause*)(memory+at);
		new (clause) Clause;
		at += sz_clause(length);
		clause->header = {0, learnt, (unsigned)length};
		clause->w = w;
		clause->mxcoef = *max_element(coefs.begin(), coefs.end());
		clause->act = 0;
		for(int i=0;i<length;i++)clause->lits()[i]=lits[i];
		for(int i=0;i<length;i++)clause->coefs()[i]=coefs[i];
		return {(uint32_t)(at-sz_clause(length))};
	}
	Clause& operator[](CRef cr) { return (Clause&)*(memory+cr.ofs); }
	const Clause& operator[](CRef cr) const { return (Clause&)*(memory+cr.ofs); }
} ca;
// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
int verbosity = 1;
// currently, the maximum number of variables is hardcoded (variable N), and most arrays are of fixed size.
const int N = 250000;
int n;
vector<CRef> clauses, learnts;
struct Watch {
	CRef cref;
};
vector<Watch> _adj[2*N+1], *adj=_adj+N;
CRef _Reason[2*N+1], *Reason=_Reason+N;
vector<int> trail;
int _Level[2*N+1], *Level=_Level+N;
vector<int> trail_lim;
int qhead; // for unit propagation
int phase[N+1];
void newDecisionLevel() { trail_lim.push_back(trail.size()); }
int decisionLevel() { return trail_lim.size(); }
double initial_time;
int NCONFL=0, NDECIDE=0;
long long NPROP=0, NIMPL=0;
int nbclausesbeforereduce=2000;
// VSIDS ---------------------------------------------------------------
double var_decay=0.95;
double var_inc=1.0;
double activity[N+1];
struct{
	// segment tree (fast implementation of priority queue).
	int tree[4*(N+1)];
	int h;
	void init(int n) {
		h=0;while((1<<h)<n+1)h++;
		fill(tree,tree+(1<<(h+1)),-1);
	}
	void percolateUp(int x) {
		for(int at=x|(1<<h); at>1; at>>=1){
			if(tree[at^1]==-1 || activity[x]>activity[tree[at^1]])tree[at>>1]=x;else break;
		}
	}
	bool empty() { return tree[1] == -1; }
	void insert(int x) {
		tree[x | (1 << h)] = x;
		percolateUp(x);
	}
	int removeMin() {
		int x = tree[1];
		assert(~x);
		tree[x|(1<<h)] = -1;
		for(int at=x|(1<<h); at>1; at>>=1){
			if(~tree[at^1] && (tree[at]==-1 || activity[tree[at^1]]>activity[tree[at]]))tree[at>>1]=tree[at^1];else tree[at>>1]=tree[at];
		}
		return x;
	}
	bool inHeap(int v) { return ~tree[v | (1 << h)]; }
} order_heap;
void insertVarOrder(int x) {
	if (!order_heap.inHeap(x)) order_heap.insert(x); }

void varDecayActivity() { var_inc *= (1 / var_decay); }
void varBumpActivity(int v){
	if ( (activity[v] += var_inc) > 1e100 ) {
		// Rescale:
		for (int i = 1; i <= n; i++)
			activity[i] *= 1e-100;
		var_inc *= 1e-100; }

	// Update order_heap with respect to new activity:
	if (order_heap.inHeap(v))
		order_heap.percolateUp(v); }
// CLAUSE VSIDS --------------------------------------------------------
double cla_inc=1.0;
double clause_decay=0.999;
void claDecayActivity() { cla_inc *= (1 / clause_decay); }
void claBumpActivity (Clause& c) {
		if ( (c.act += cla_inc) > 1e20 ) {
			// Rescale:
			for (size_t i = 0; i < learnts.size(); i++)
				c.act *= 1e-20;
			cla_inc *= 1e-20; } }
// ---------------------------------------------------------------------
// ---------------------------------------------------------------------

template<class A,class B> long long slack(int length,A const& lits,B const& coefs,long long w){
	long long s=-w;
	for(int i=0;i<length;i++){
		int l = lits[i];
		int coef = coefs[i];
		if(Level[-l]==-1)s+=coef;
	}
	return s;
}

long long slack(Clause & C){ return slack(C.size(),C.lits(),C.coefs(),C.w); }

void attachClause(CRef cr){
	Clause & C = ca[cr];
	vector<int>coefs2(C.coefs(),C.coefs()+C.size());sort(coefs2.begin(),coefs2.end());
	// determine k, the minimum number of literals such that satisfying any k is enough to satisfy the constraint.
	int k=0;
	long long sum=0;
	for(int c:coefs2){sum+=c;k++;if(sum>=C.w)break;}
	if (sum < C.w) exit_UNSAT();
	C.nwatch = min((int) C.size(), k+1);
	// sort literals by the decision level at which they were falsified, descending order (never falsified = level infinity)
	vector<pair<int,int>> order;
	for(int i=0;i<(int)C.size();i++){
		int lvl=Level[-C.lits()[i]]; if(lvl==-1)lvl=1e9;
		order.emplace_back(-lvl,i);
	}
	sort(order.begin(),order.end());
	vector<int>lits_old (C.lits(), C.lits()+C.size());
	vector<int>coefs_old (C.coefs(), C.coefs()+C.size());
	// watch the first k literals in this order (we may be watching falsified literals).
	// it can be proven that this gives a "valid state" for the watches.
	for(int i=0;i<(int)C.size();i++){
		C.lits()[i] = lits_old[order[i].second];
		C.coefs()[i] = coefs_old[order[i].second];
	}
	for(int i=0;i<C.nwatch;i++) adj[C.lits()[i]].push_back({cr});
}

bool locked(CRef cr){
	Clause & c = ca[cr];
	for(size_t idx=0;idx<c.size();idx++){
		if(Reason[c.lits()[idx]] == cr) return true;
	}
	return false;
}

void removeClause(CRef cr){
	Clause& c = ca[cr];
	assert(!c.markedfordel());
	assert(!locked(cr));
	c.markfordel();
	ca.wasted += ca.sz_clause(c.size());
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
void uncheckedEnqueue(int p, CRef from){
	assert(Level[p]==-1 && Level[-p]==-1);
	Level[p] = decisionLevel();
	Reason[p] = from;
	trail.push_back(p);
}

void undoOne(){
	assert(!trail.empty());
	int l = trail.back();
	trail.pop_back();
	Level[l] = -1;
	phase[abs(l)]=l;
	if(!trail_lim.empty() && trail_lim.back() == (int)trail.size())trail_lim.pop_back();
	Reason[l] = CRef_Undef;
	insertVarOrder(abs(l));
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
/**
 * In the conflict analysis we represent the learnt clause
 * by an array of length 2*N, with one position per literal.
 * 
 * After each analyze() we want to reset this array.
 * Because this is expensive we keep track of which literals participate
 * in the analysis and reset only their coefficients.
 */
struct ConflictData {
	long long slack;
	int cnt_falsified_currentlvl;
	// here we use int64 because we could get overflow in the following case:
	// the reason's coefs multiplied by the coef. of the intermediate conflict clause
	long long _M[2*N+1], *M=_M+N;
	long long w;
	bool used[N+1];
	vector<int> usedlist;
	void init(){
		memset(_M,0,sizeof _M);
		memset(used,0,sizeof used);
		usedlist.reserve(n);
	}
	void reset(){
		for(int x:usedlist)M[x]=M[-x]=0,used[x]=false;
		usedlist.clear();
	}
	void use(int x){
		if(!used[x])used[x]=true,usedlist.push_back(x);
	}
} confl_data;

inline long long ceildiv(long long p,long long q){ return (p+q-1)/q; }

void round_reason(int l0, vector<int>&out_lits,vector<int>&out_coefs,int&out_w) {
	Clause & C = ca[Reason[l0]];
	int old_coef_l0 = C.coefs()[find(C.lits(),C.lits()+C.size(),l0)-C.lits()];
	int w = C.w;
	for(size_t i=0;i<C.size();i++){
		int l = C.lits()[i];
		int coef = C.coefs()[i];
		if (Level[-l] == -1) {
			if (coef % old_coef_l0 != 0) w -= coef;
			else out_lits.push_back(l), out_coefs.push_back(coef / old_coef_l0);
			
			// partial weakening would instead do:
			/*w -= coef % old_coef_l0;
			if (coef >= old_coef_l0) out_lits.push_back(l), out_coefs.push_back(coef / old_coef_l0);*/
		} else {
			out_lits.push_back(l), out_coefs.push_back(ceildiv(coef, old_coef_l0));
		}
	}
	out_w = ceildiv(w, old_coef_l0);
	assert(slack(out_lits.size(), out_lits, out_coefs, out_w) == 0);
}

void round_conflict(long long c) {
	for(int x:confl_data.usedlist)for(int l=-x;l<=x;l+=2*x)if(confl_data.M[l]){
		if (Level[-l] == -1) {
			if (confl_data.M[l] % c != 0) {
				confl_data.w -= confl_data.M[l], confl_data.M[l] = 0;
			} else confl_data.M[l] /= c;
			
			// partial weakening would instead do:
			/*confl_data.w -= confl_data.M[l] % c;
			confl_data.M[l] /= c;*/
		} else confl_data.M[l] = ceildiv(confl_data.M[l], c);
	}
	confl_data.w = ceildiv(confl_data.w, c);
	confl_data.slack = -ceildiv(-confl_data.slack, c);
}

void clashing_addition(int l0, vector<int>&reason_lits,vector<int>&reason_coefs,int&reason_w){
	long long * M = confl_data.M;
	long long & w = confl_data.w;
	w += reason_w;
	bool overflow = false;
	for(size_t it=0;it<reason_lits.size();it++){
		int l = reason_lits[it];
		int c = reason_coefs[it];
		confl_data.use(abs(l));
		if (M[-l] > 0) {
			if (c >= M[-l]) {
				if (Level[l] == decisionLevel()) confl_data.cnt_falsified_currentlvl--;
				M[l] = c - M[-l];
				w -= M[-l];
				M[-l] = 0;
				if (Level[-l] == decisionLevel() && M[l] > 0) confl_data.cnt_falsified_currentlvl++;
			} else {
				M[-l] -= c;
				w -= c;
			}
		} else {
			if (Level[-l] == decisionLevel() && M[l] == 0) confl_data.cnt_falsified_currentlvl++;
			M[l] += c;
		}
		if (M[l] > (int) 1e9) overflow = true;
	}
	if (w > (int) 1e9 || overflow) {
		// round to cardinality.
		long long d = 0;
		for(int x:confl_data.usedlist)for(int l=-x;l<=x;l+=2*x)d=max(d, confl_data.M[l]);
		round_conflict(d);
	}
}

int computeLBD(CRef cr) {
	Clause & C = ca[cr];
	set<int> levels;
	int * lits = C.lits();
	for (int i=0; i<(int)C.size(); i++) if (~Level[-lits[i]]) levels.insert(Level[-lits[i]]);
	return (int) levels.size();
}

void analyze(CRef confl, vector<int>& out_lits, vector<int>& out_coefs, int& out_w){
	Clause & C = ca[confl];
	confl_data.slack = slack(C);
	confl_data.cnt_falsified_currentlvl = 0;
	confl_data.w = C.w;
	for(size_t i=0;i<C.size();i++){
		int l = C.lits()[i];
		int coef = C.coefs()[i];
		confl_data.use(abs(l));
		confl_data.M[l]=coef;
		if (Level[-l] == decisionLevel()) confl_data.cnt_falsified_currentlvl++;
	}
	if (C.learnt() && C.lbd > 2) C.lbd = min(C.lbd, computeLBD(confl));
	vector<int> reason_lits; reason_lits.reserve(n);
	vector<int> reason_coefs; reason_coefs.reserve(n);
	int reason_w;
	while(1){
		if (decisionLevel() == 0) {
			exit_UNSAT();
		}
		int l = trail.back();
		if(confl_data.M[-l]) {
			confl_data.M[-l] = min(confl_data.M[-l], confl_data.w); // so that we don't round the conflict if w=1.
			if (confl_data.M[-l] > 1) {
				round_conflict(confl_data.M[-l]);
			}
			if (confl_data.cnt_falsified_currentlvl == 1) {
				break;
			} else {
				if (ca[Reason[l]].learnt()) {
					claBumpActivity(ca[Reason[l]]);
					if (ca[Reason[l]].lbd > 2) ca[Reason[l]].lbd = min(ca[Reason[l]].lbd, computeLBD(Reason[l]));
				}
				reason_lits.clear();
				reason_coefs.clear();
				round_reason(l, reason_lits, reason_coefs, reason_w);
				clashing_addition(l, reason_lits, reason_coefs, reason_w);
			}
		}
		int oldlvl=decisionLevel();
		undoOne();
		if(decisionLevel()<oldlvl){
			for(int x:confl_data.usedlist)for(int l=-x;l<=x;l+=2*x)if(confl_data.M[l]) {
				if (Level[-l] == decisionLevel()) confl_data.cnt_falsified_currentlvl++;
			}
		}
	}
	for(int x:confl_data.usedlist)varBumpActivity(x);
	for(int x:confl_data.usedlist)for(int l=-x;l<=x;l+=2*x)if(confl_data.M[l]){
		out_lits.push_back(l),out_coefs.push_back(min(confl_data.M[l],confl_data.w));
	}
	out_w=confl_data.w;
	confl_data.reset();
}

/**
 * Unit propagation with watched literals.
 * 
 * post condition: the propagation queue is empty (even if there was a conflict).
 */
CRef propagate() {
	CRef confl = CRef_Undef;
	while(qhead<(int)trail.size()){
		int p=trail[qhead++];
		vector<Watch> & ws = adj[-p];
		vector<Watch>::iterator i, j, end;
		for(i = j = ws.begin(), end = ws.end(); i != end;){
			CRef cr = i->cref;
			i++;
			Clause & C = ca[cr];
			if(C.header.markedfordel)continue;
			int nwatch = C.nwatch;
			int * lits = C.lits();
			int * coefs = C.coefs();
			int pos = 0; while (lits[pos] != -p) pos++;
			// first, try to replace the falsified watch.
			bool found=false;
			for(int it=nwatch;it<(int)C.size() && !found;it++)if(Level[-lits[it]]==-1){
				adj[lits[it]].push_back({cr});
				swap(lits[it],lits[pos]),swap(coefs[it],coefs[pos]);
				found=true;
			}
			if(found)continue;
			*j++ = {cr};
			long long s = slack(nwatch,lits,coefs,C.w);
			if(s<0){
				confl = cr;
				qhead = trail.size();
				while(i<end)*j++=*i++;
			}else if (s < C.mxcoef){ // this check is an optimization
				for(int it=0;it<nwatch;it++)if(Level[-lits[it]]==-1 && coefs[it] > s){
					NIMPL++;
					if (Level[lits[it]]==-1) {
						uncheckedEnqueue(lits[it], cr);
						NPROP++;
					}
				}
			}
		}
		ws.erase(j, end);
	}
	return confl;
}

int pickBranchLit(){
	int next = 0;

	// Activity based decision:
	while (next == 0 || ~Level[next] || ~Level[-next])
		if (order_heap.empty()){
			next = 0;
			break;
		}else
			next = order_heap.removeMin();

	return next == 0 ? 0 : phase[next];
}

void checksol() {
	for(int i=1;i<=n;i++)assert(~Level[i] || ~Level[-i]);
	for(CRef cr : clauses)assert(slack(ca[cr]) >= 0);
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
void init(int nvars){
	if (nvars < 0){
		printf("Error: The number of variables is negative.\n");
		exit(1);
	}
	if (nvars > N){
		printf("Error: The number of variables exceeds the default limit.\n");
		exit(1);
	}
	n = nvars;
	qhead=0;
	order_heap.init(nvars);
	for(int i=1;i<=n;i++){
		Level[i]=Level[-i]=-1;
		Reason[i]=Reason[-i]=CRef_Undef;
		phase[i]=-i;
		activity[i]=0;
		insertVarOrder(i);
		//adj[i].clear(); adj[-i].clear(); // is already cleared.
	}
	confl_data.init();
	ca.memory = NULL;
	ca.at = 0;
	ca.cap = 0;
	ca.wasted = 0;
	ca.capacity(1024*1024);//4MB
}

void reduce_by_toplevel(vector<int>& lits, vector<int>& coefs, int& w){
	size_t i,j;
	for(i=j=0; i<lits.size(); i++){
		if(Level[ lits[i]]==0) w-=coefs[i]; else
		if(Level[-lits[i]]==0); else {
			lits[j]=lits[i];
			coefs[j]=coefs[i];
			j++;
		}
	}
	lits.erase(lits.begin()+j,lits.end());
	coefs.erase(coefs.begin()+j,coefs.end());
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
// Parsers
void process_ineq(vector<int> lits, vector<int> coefs, int w){
	for(size_t i=0;i<lits.size();i++){
		if(coefs[i] < 0) lits[i]*=-1,coefs[i]*=-1,w+=coefs[i];
	}
	reduce_by_toplevel(lits,coefs,w);
	if(w <= 0)return;//already satisfied.
	long long som = 0;for(int c:coefs)som+=c;
	if(som < w)puts("c UNSAT trivially inconsistent constraint"),exit_UNSAT();
	for(size_t i=0;i<lits.size();i++)if(som-coefs[i] < w){
		//printf("propagate %d\n",lits[i]);
		uncheckedEnqueue(lits[i],CRef_Undef);
	}
	reduce_by_toplevel(lits,coefs,w);
	if(w <= 0)return;//already satisfied.
	CRef cr = ca.alloc(lits, coefs, w, false);
	attachClause(cr);
	clauses.push_back(cr);
	if (propagate() != CRef_Undef)puts("c UNSAT initial UP"),exit_UNSAT();
}

/*
 * Note: the OPB parser does not report most errors.
 * Unsupported is e.g.
 * - Negated literals like "~x1"; instead, one could use negative coefficients "-x1"
 * - Nonlinear constraints like "+1 x1 x2 +1 x3 x4 >= 1;"
 */
void opb_read(istream & in) {
	for (string line; getline(in, line);) {
		if (line.empty()) continue;
		else if (line[0] == '*') {
			if (line.substr(0, 13) == "* #variable= ") {
				istringstream is (line.substr(13));
				int n;
				if (!(is >> n)) {
					printf("Error: Couldn't parse header\n");
					exit(1);
				}
				init(n);
			}
		} else {
			string symbol;
			if (line.find(">=") != string::npos) symbol = ">=";
			else symbol = "=";
			assert(line.find(symbol) != string::npos);
			istringstream is (line.substr(0, line.find(symbol)));
			vector<int> lits;
			vector<int> coefs;
			int coef;
			string var;
			while (is >> coef >> var) {
				assert(coef != 0 && abs(coef) <= (int) 1e9);
				int x = atoi(var.substr(1).c_str());
				lits.push_back(x);
				coefs.push_back(coef);
			}
			int w = atoi(line.substr(line.find("=") + 1).c_str());
			process_ineq(lits, coefs, w);
			// Handle equality case with two constraints
			if (line.find(" = ") != string::npos) {
				for (int & coef : coefs) coef = -coef;
				w *= -1;
				process_ineq(lits, coefs, w);
			}
		}
	}
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
// We assume in the garbage collection method that reduceDB() is the
// only place where clauses are deleted.
void garbage_collect(){
	if (verbosity > 0) puts("c GARBAGE COLLECT");
	for(int l=-n; l<=n; l++) {
		size_t i, j;
		for(i=0,j=0;i<adj[l].size();i++){
			CRef cr = adj[l][i].cref;
			if(!ca[cr].markedfordel())adj[l][j++]=adj[l][i];
		}
		adj[l].erase(adj[l].begin()+j,adj[l].end());
	}
	// clauses, learnts, adj[-n..n], reason[-n..n].
	uint32_t ofs_learnts=0;for(CRef cr:clauses)ofs_learnts+=ca.sz_clause(ca[cr].size());
	sort(learnts.begin(), learnts.end(), [](CRef x,CRef y){return x.ofs<y.ofs;}); // we have to sort here, because reduceDB shuffles them.
	ca.wasted=0;
	ca.at=ofs_learnts;
	vector<CRef> learnts_old = learnts;
	for(CRef & cr : learnts){
		size_t length = ca[cr].size();
		memmove(ca.memory+ca.at, ca.memory+cr.ofs, sizeof(uint32_t)*ca.sz_clause(length));
		cr.ofs = ca.at;
		ca.at += ca.sz_clause(length);
	}
	#define update_ptr(cr) if(cr.ofs>=ofs_learnts)cr=learnts[lower_bound(learnts_old.begin(), learnts_old.end(), cr)-learnts_old.begin()]
	for(int l=-n; l<=n; l++)for(size_t i=0;i<adj[l].size();i++)update_ptr(adj[l][i].cref);
	for(int l=-n;l<=n;l++)if(Reason[l]!=CRef_Undef)update_ptr(Reason[l]);
	#undef update_ptr
}

struct reduceDB_lt {
    bool operator () (CRef x, CRef y) { 
 
    // Main criteria... Like in MiniSat we keep all binary clauses
    if(ca[x].size()> 2 && ca[y].size()==2) return 1;
    
    if(ca[y].size()>2 && ca[x].size()==2) return 0;
    if(ca[x].size()==2 && ca[y].size()==2) return 0;
    
    // Second one  based on literal block distance
    if(ca[x].lbd> ca[y].lbd) return 1;
    if(ca[x].lbd< ca[y].lbd) return 0;    
    
    
    // Finally we can use old activity or size, we choose the last one
        return ca[x].act < ca[y].act;
	//return x->size() < y->size();

        //return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity()); } 
    }    
};
void reduceDB(){
	size_t i, j;

	sort(learnts.begin(), learnts.end(), reduceDB_lt());
	if(ca[learnts[learnts.size() / 2]].lbd<=3) nbclausesbeforereduce += 1000;
	// Don't delete binary or locked clauses. From the rest, delete clauses from the first half
	// and clauses with activity smaller than 'extra_lim':
	for (i = j = 0; i < learnts.size(); i++){
		Clause& c = ca[learnts[i]];
		if (c.lbd>2 && c.size() > 2 && !locked(learnts[i]) && i < learnts.size() / 2)
			removeClause(learnts[i]);
		else
			learnts[j++] = learnts[i];
	}
	learnts.erase(learnts.begin()+j,learnts.end());
	if ((double) ca.wasted / (double) ca.at > 0.2) garbage_collect();
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
static double luby(double y, int x){

	// Find the finite subsequence that contains index 'x', and the
	// size of that subsequence:
	int size, seq;
	for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

	while (size-1 != x){
		size = (size-1)>>1;
		seq--;
		x = x % size;
	}

	return pow(y, seq);
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------

bool asynch_interrupt = false;
static void SIGINT_interrupt(int signum){
	asynch_interrupt = true;
}

static void SIGINT_exit(int signum){
	printf("\n"); printf("*** INTERRUPTED ***\n");
	exit(1);
}

void print_stats() {
	printf("c CPU time			  : %g s\n", cpuTime()-initial_time);
	printf("d decisions %d\n", NDECIDE);
	printf("d conflicts %d\n", NCONFL);
	printf("d propagations %lld\n", NPROP);
}

void exit_SAT() {
	checksol();
	puts("c SATISFIABLE (checked)");
	print_stats();
	puts("s SATISFIABLE");
	printf("v");for(int i=1;i<=n;i++)if(~Level[i])printf(" x%d",i);else printf(" -x%d",i);printf("\n");
	exit(10);
}

void exit_UNSAT() {
	print_stats();
	puts("s UNSATISFIABLE");
	exit(20);
}

void exit_INDETERMINATE() {
	print_stats();
	puts("s UNKNOWN");
	exit(0);
}

void usage(int argc, char**argv) {
	printf("Usage: %s [OPTION] instance.opb\n", argv[0]);
	printf("\n");
	printf("Options:\n");
	printf("  -h [ --help ]                Prints this help message\n");
	printf("  -v [ --verbosity ] arg (=1)  Set the verbosity of the output.\n");
}

int main(int argc, char**argv){
	char * filename = 0;
	{
		static struct option long_options[] =
		{
			{"help",      no_argument, 0, 'h'},
			{"verbosity", required_argument, 0, 'v'},
			{0, 0, 0, 0}
		};
		int c;
		int option_index = 0;
		while ((c = getopt_long (argc, argv, "hv:", long_options, &option_index)) != -1) {
			switch (c)
			{
				case 'h':
					usage(argc, argv);
					exit(0);
				case 'v':
					verbosity = atoi(optarg);
					break;
				default:
					abort();
			}
		}
		if (optind < argc) {
			filename = argv[optind];
		}
	}
	initial_time = cpuTime();
	signal(SIGINT, SIGINT_exit);
	signal(SIGXCPU,SIGINT_exit);
	if (filename != 0) {
		ifstream fin (filename);
		if (!fin) {
			printf("Error: Couldn't open file %s\n", filename);
			exit(1);
		}
		opb_read(fin);
	} else {
		if (verbosity > 0) printf("c No filename given, reading from standard input\n");
		opb_read(cin);
	}
	signal(SIGINT, SIGINT_interrupt);
	signal(SIGXCPU,SIGINT_interrupt);
	double restart_inc = 2;
	int restart_first = 100;
	int curr_restarts=0;
	int nconfl_to_restart=0;
	//reduceDB:
	int cnt_reduceDB=1;
	int incReduceDB=300;
	while (true) {
		CRef confl = propagate();
		if (confl != CRef_Undef) {
			have_confl:
			varDecayActivity();
			claDecayActivity();
			if (decisionLevel() == 0) {
				exit_UNSAT();
			}
			NCONFL++; nconfl_to_restart--;
			if(NCONFL%1000==0){
				if (verbosity > 0) {
					printf("c #Conflicts: %10d | #Learnt: %10d\n",NCONFL,(int)learnts.size());
					// memory usage
					cout<<"c total clause space: "<<ca.cap*4/1024./1024.<<"MB"<<endl;
					cout<<"c total #watches: ";{int cnt=0;for(int l=-n;l<=n;l++)cnt+=(int)adj[l].size();cout<<cnt<<endl;}
					printf("c total #propagations: %lld / total #impl: %lld (eff. %.3lf)\n",NPROP,NIMPL,(double)NPROP/(double)NIMPL);
				}
			}
			vector<int>lits;vector<int>coefs;int w;
			analyze(confl, lits, coefs, w);
			reduce_by_toplevel(lits,coefs,w);
			// compute an assertion level
			// it may be possible to backjump further, but we don't do this
			int lvl = 0;
			for (int i=0; i<(int)lits.size(); i++)
				if (Level[-lits[i]] < decisionLevel())
					lvl = max(lvl, Level[-lits[i]]);
			assert(lvl < decisionLevel());
			CRef cr = ca.alloc(lits,coefs,w, true);
			Clause & C = ca[cr];
			C.lbd = computeLBD(cr);
			while(decisionLevel()>lvl)undoOne();
			qhead=trail.size();
			learnts.push_back(cr);
			attachClause(cr);
			if (::slack(C) == 0) {
				for (int i=0; i<(int)lits.size(); i++)
					if (Level[-lits[i]] == -1 && Level[lits[i]] == -1)
						uncheckedEnqueue(lits[i], cr);
			} else {
				// the learnt constraint is conflicting at the assertion level.
				// in this case, immediately enter a new conflict analysis again.
				confl = cr;
				goto have_confl;
			}
		} else {
			if(asynch_interrupt)exit_INDETERMINATE();
			if(nconfl_to_restart <= 0){
				while(decisionLevel()>0)undoOne();
				qhead = trail.size();
				double rest_base = luby(restart_inc, curr_restarts++);
				nconfl_to_restart = rest_base * restart_first;
			}
			//if ((int)learnts.size()-(int)trail.size() >= max_learnts)
			if(NCONFL >= cnt_reduceDB * nbclausesbeforereduce) {
				reduceDB();
				cnt_reduceDB++;
				nbclausesbeforereduce += incReduceDB;
			}
			int next = pickBranchLit();
			if(next==0)exit_SAT();
			newDecisionLevel();
			NDECIDE++;
			uncheckedEnqueue(next,CRef_Undef);
		}
	}
}
