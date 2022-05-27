#ifndef _simplify_h_INCLUDED
#define _simplify_h_INCLUDED

#include "map.h"
using namespace std;
#define MAX_XOR 6
typedef long long ll;

struct xorgate {
    xorgate(int _c, int _rhs, int _sz) {
        c = _c, rhs = _rhs, sz = _sz;
    }
public:
    int c;
    int rhs;
    int sz;
};

struct simplify {
public:   
    simplify();
    int vars;
    int clauses;
    svec<svec<int>> clause, res_clause;
    string infile;
    void readfile(const char *file);
    void release();
    
    // simplify data structure
    int maxlen, orivars, oriclauses, res_clauses, resolutions;
    int *f, nlit, *a, *val, *color, *varval, *q, *seen, *resseen, *clean, *mapto, *mapfrom, *mapval;
    Map<ll, int> C;
    svec<int> *occurp, *occurn, clause_delete, nxtc, resolution;

    ll mapv(int a, int b);
    int find(int x);    
    bool res_is_empty(int var);
    void update_var_clause_label();
    void simplify_init();
    bool simplify_resolution();
    bool simplify_binary();
    bool simplify_easy_clause();
    void print_complete_model();

    int *abstract;
    int gauss_eli_unit;
    int gauss_eli_binary;
    svec<xorgate> xors;
    svec<int> scc_id;
    svec<svec<int>> scc;
    svec<svec<int>> xor_scc;
    bool simplify_gauss();
    int  search_xors();
    int  cal_dup_val(int i);
    int  ecc_var();
    int  ecc_xor();
    int  gauss_elimination();

    svec<svec<int>> card_one;
    svec<svec<double>> mat;
    svec<int> *occur;
    svec<int> cdel;
    int  check_card(int id);
    int  simplify_card();
    int  search_almost_one();    
    int  card_elimination();
    int  scc_almost_one();
    void upd_occur(int v, int s);
};

#endif