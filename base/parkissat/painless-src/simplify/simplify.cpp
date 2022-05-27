#include "simplify.h"
#include <algorithm>
#include <m4ri/m4ri.h>
using namespace std;
#define TOLIT(x) ((x) > 0 ? (x) : ((-x) + vars))
#define NEG(x) ((x) > vars ? ((x) - vars) : ((x) + vars))

simplify::simplify():
  vars                  (0),
  clauses               (0),
  maxlen                (0)
{}


inline int pnsign(int x) {
    return (x > 0 ? 1 : -1);
}
inline int sign(int x) {
    return x % 2 == 1 ? -1 : 1;
}
inline int tolit(int x) {
    if (x > 0) return x * 2;
    else return (-x) * 2 + 1;
}
inline int toidx(int x) {
    return (x & 1 ? -(x >> 1) : (x >> 1));
}
inline int reverse(int x) {
    if (x % 2 == 1) return x - 1;
    else return x + 1;
}
inline ll simplify::mapv(int a, int b) {
    return 1ll * a * nlit + (ll)b;
}
int simplify::find(int x) {
    if (f[x] == x) return x;
    int fa = f[x];
    f[x] = find(fa);
    val[x] = val[fa] * val[x];
    return f[x];
}
void simplify::simplify_init() {
    f = new int[vars + 10];
    val = new int[vars + 10];
    color = new int[vars + 10];
    varval = new int[vars + 10];
    q = new int[vars + 10];
    clean = new int[vars + 10];
    seen = new int[(vars << 1) + 10];
    clause_delete.growTo(clauses+1, 0);
    nxtc.growTo(clauses+1, 0);
    abstract = new int[clauses + 10];
    occurp = new svec<int>[vars + 1];
    occurn = new svec<int>[vars + 1]; 
    for (int i = 1; i <= clauses; i++) {
        int l = clause[i].size();
        maxlen = max(maxlen, l);
    }
    resseen = new int[(vars << 1) + 10];
    a = new int[maxlen + 1];

    mapval = new int[vars + 10];
    mapto = new int[vars + 10];
    for (int i = 1; i <= vars; i++) mapto[i] = i, mapval[i] = 0;
}

void simplify::release() {
    delete []f;
    delete []val;
    delete []color;
    delete []varval;
    delete []q;
    delete []clean;
    delete []seen;
    clause_delete.clear(true);
    nxtc.clear(true);
    delete []abstract;
    delete []resseen;   
    delete []a;
    delete []mapfrom; 
    for (int i = 0; i <= vars; i++)
        occurp[i].clear(true), occurn[i].clear(true);
    delete []occurp;
    delete []occurn;
    C.clear();
}

int simplify::search_almost_one() {
    nlit = 2 * vars + 2;
    occur = new svec<int>[nlit]; 
    for (int i = 1; i <= clauses; i++) {
        clause_delete[i] = 0;
        if (clause[i].size() != 2) continue;
        int x = tolit(clause[i][0]);
        int y = tolit(clause[i][1]);
        ll id1 = mapv(x, y);
        ll id2 = mapv(y, x);
        C.insert(id1, i);
        C.insert(id2, i);
        occur[x].push(y);
        occur[y].push(x);
    }
    for (int i = 1; i <= vars; i++) {
        seen[i * 2] = seen[i * 2 + 1] = color[i] = 0;
    }
    int t = 0;
    svec<int> ino, nei;
    for (int i = 2; i <= vars * 2 + 1; i++) {
        if (seen[i] || !occur[i].size()) continue;
        seen[i] = 1;
        nei.clear();
        for (int j = 0; j < occur[i].size(); j++)
            if (!seen[occur[i][j]])
                nei.push(occur[i][j]);
        do {
            ino.clear();
            ino.push(i);
            for (int j = 0; j < nei.size(); j++) {
                int v = nei[j], flag = 1;
                for (int k = 0; k < ino.size(); k++) {
                    ll id = mapv(v, ino[k]);
                    int d1 = C.get(id, 0);
                    if (!d1) {flag = 0; break;}
                    q[k] = d1;
                }
                if (flag) {
                    for (int k = 0; k < ino.size(); k++) {
                        clause_delete[q[k]] = 1;
                        ll id1 = mapv(v, ino[k]), id2 = mapv(ino[k], v);
                        C.remove(id1);
                        C.remove(id2);
                    }
                    ino.push(v);
                }
            }
            if (ino.size() >= 2) {
                card_one.push();
                for (int j = 0; j < ino.size(); j++) {
                    card_one[card_one.size() - 1].push(-toidx(ino[j]));
                }
            }
        } while (ino.size() != 1);
    }
    for (int i = 0; i < nlit; i++)
        occur[i].clear(true);
    delete []occur;
    return card_one.size();
}

void simplify::upd_occur(int v, int s) {
    int x = abs(v);
    int t = 0;
    if (v > 0) {
        for (int j = 0; j < occurp[x].size(); j++)
            if (occurp[x][j] != s) occurp[x][t++] = occurp[x][j]; 
        assert(t == occurp[x].size() - 1);
        occurp[x].setsize(t);
    }
    else {
        for (int j = 0; j < occurn[x].size(); j++)
            if (occurn[x][j] != s) occurn[x][t++] = occurn[x][j];
        assert(t == occurn[x].size() - 1);
        occurn[x].setsize(t);
    }
}

int simplify::scc_almost_one() {
    for (int i = 1; i <= vars; i++) {
        occurp[i].clear();
        occurn[i].clear();
    }
    cdel.growTo(card_one.size(), 0);
    for (int i = 0; i < card_one.size(); i++) {
        for (int j = 0; j < card_one[i].size(); j++)
            if (card_one[i][j] > 0)
                occurp[card_one[i][j]].push(i);
            else 
                occurn[-card_one[i][j]].push(i);
    }
    int flag = 1;
    do {
        flag = 0;
        for (int i = 1; i <= vars; i++) {
            if (!occurp[i].size() || !occurn[i].size()) continue;
            if (card_one.size() + occurp[i].size() * occurp[i].size() > 1e7 / vars) return 0;
            flag = 1;
            for (int ip = 0; ip < occurp[i].size(); ip++) 
                cdel[occurp[i][ip]] = 1;
            for (int in = 0; in < occurn[i].size(); in++) 
                cdel[occurn[i][in]] = 1;
            for (int ip = 0; ip < occurp[i].size(); ip++) {
                int op = occurp[i][ip];
                for (int in = 0; in < occurn[i].size(); in++) {
                    int on = occurn[i][in];
                    card_one.push();
                    cdel.push(0);
                    int id = card_one.size() - 1;
                    for (int j = 0; j < card_one[op].size(); j++) {
                        int v = card_one[op][j];
                        if (abs(v) != i) {
                            card_one[id].push(v);
                            if (v > 0) occurp[v].push(id);
                            else occurn[-v].push(id);
                        }
                    }
                    for (int j = 0; j < card_one[on].size(); j++) {
                        int v = card_one[on][j];
                        if (abs(v) != i) {
                            card_one[id].push(v);
                            if (v > 0) occurp[v].push(id);
                            else occurn[-v].push(id);
                        }
                    }
                }
            }
            for (int ip = 0; ip < occurp[i].size(); ip++) {
                int op = occurp[i][ip];
                for (int j = 0; j < card_one[op].size(); j++)
                    upd_occur(card_one[op][j], op);
            }
            
            for (int in = 0; in < occurn[i].size(); in++) {
                int on = occurn[i][in];
                for (int j = 0; j < card_one[on].size(); j++)
                    upd_occur(card_one[on][j], on);
            }
        }       
    } while(flag);
    int t = 0;
    for (int i = 0 ; i < card_one.size(); i++) {
        if (cdel[i]) continue;
        ++t;
    }
    return t;
}

int simplify::check_card(int id) { //0: wrong  -1:useless    1:normal
    int ps = 0, ns = 0, t = -1;
    double poss = 0, negs = 0;
    for (int j = 1; j <= vars; j++) {
        if (fabs(mat[id][j]) < 1e-6) continue;
        t = j;
        if (mat[id][j] > 0) ++ps, poss += mat[id][j];
        if (mat[id][j] < 0) ++ns, negs += mat[id][j];
    }
    if (ns + ps == 1) {
        double r = mat[id][0] / mat[id][t];
        if (ps) {
            if (fabs(r) < 1e-6);
            else if (r < 0) {
                return 0;
            }
            return -1;
        }
        if (ns) {
            if (fabs(r - 1) < 1e-6);
            else if (r > 1) {
                return 0;
            }
            return -1;
        }
    }
    if (ns + ps == 0) {
        if (mat[id][0] < -(1e-6)) {
            return 0;
        }
        return -1;   
    }
    if (poss <= mat[id][0]) {
        return -1;
    }
    if (negs >= mat[id][0]) {
        if (negs == mat[id][0]) {
            //unit
        }
        else return 0;
    }
    if (mat[id][0] == 0) {
        if (ps == 0) {
            return -1;
        }
        else if (ns == 0) {
            //unit
        }
    }
    return 1;
}

int simplify::card_elimination() {
    //sigma aixi <= b
    svec<int> row_size;
    for (int i = 0; i < card_one.size(); i++) {
        if (cdel[i]) continue;
        int b = 1;
        mat.push();
        row_size.push(card_one[i].size());
        int id = mat.size() - 1;
        mat[id].growTo(vars + 1, 0);
        for (int j = 0; j < card_one[i].size(); j++) {
            if (card_one[i][j] < 0) b--;
            mat[id][abs(card_one[i][j])] += pnsign(card_one[i][j]);
        }
        mat[id][0] = b;
    }
    for (int i = 0; i < card_one.size(); i++)
        card_one[i].clear(true);
    card_one.clear(true);
    cdel.clear(true);   
    for (int i = 1; i <= clauses; i++) {
        if (clause_delete[i]) continue;
        int b = 1;
        for (int j = 0; j < clause[i].size(); j++)
            if (clause[i][j] < 0) b--;
        //convert >= to <=
        mat.push();
        row_size.push(clause[i].size());
        int id = mat.size() - 1;
        mat[id].growTo(vars + 1, 0);
        for (int j = 0; j < clause[i].size(); j++) {
            mat[id][abs(clause[i][j])] += -pnsign(clause[i][j]);
        }
        mat[id][0] = -b;
    }
    int row = mat.size();
    svec<int> mat_del, upp, low, var_score1, var_score2;
    mat_del.growTo(row, 0);
    var_score1.growTo(vars + 1, 0);
    var_score2.growTo(vars + 1, 0);
    for (int v = 1; v <= vars; v++) {
        upp.clear();
        low.clear();
        for (int i = 0; i < row; i++) {
            if (fabs(mat[i][v]) < 1e-6) continue;
            if (mat[i][v] > 0) 
                upp.push(i);
            else
                low.push(i);
        }
        var_score1[v] = upp.size() * low.size();
        for (int i = 0; i < upp.size(); i++)
            for (int j = 0; j < low.size(); j++) 
                var_score2[v] += row_size[upp[i]] * row_size[low[j]];
    }
    svec<int> elim;
    elim.growTo(vars + 1, 0);
    for (int turn = 1; turn <= vars; turn++) {
        int v = 0;
        for (int i = 1; i <= vars; i++) {
            if (elim[i]) continue;
            if (!v) v = i;
            else {
                if (var_score1[i] < var_score1[v]) v = i;
                else if (var_score1[i] == var_score1[v] && var_score2[i] < var_score2[v])
                    v = i;
            }
        }
        elim[v] = 1;
        upp.clear();
        low.clear();
        for (int i = 0; i < row; i++) {
            if (mat_del[i]) continue;
            if (fabs(mat[i][v]) < 1e-6) continue;
            mat_del[i] = 1;
            if (mat[i][v] > 0) { 
                upp.push(i);
            }
            else {
                low.push(i);
            }
        }
        if (mat.size() + upp.size() * low.size() > 1e7/vars || mat.size() > 1e3) return 1;
        for (int iu = 0; iu < upp.size(); iu++) {
            int u = upp[iu];
            for (int il = 0; il < low.size(); il++) {
                int l = low[il];
                double b = mat[u][0] / mat[u][v] + mat[l][0] / (-mat[l][v]);
                mat.push();
                mat_del.push(0);
                int id = mat.size() - 1;
                mat[id].growTo(vars + 1, 0);
                for (int j = 0; j <= vars; j++)
                    mat[id][j] = mat[u][j] / mat[u][v] + mat[l][j] / (-mat[l][v]);
                
                int check_res = check_card(id);
                if (check_res == 0) return 0;
                if (check_res == -1) mat.pop();
            }
        }
        row = mat.size();
    }
    return 1;
}

int simplify::simplify_card() {
    int sone = search_almost_one();
    // printf("c [CE] almost one cons: %d\n", sone);
    if (!sone) return 1;
    int scc = scc_almost_one();
    int sz = card_one.size();
    for (int i = 1; i <= clauses; i++)
        if (!clause_delete[i]) ++sz;
    if (sz > 1e7 / vars || !scc || sz > 1e3) {
        for (int i = 0; i < card_one.size(); i++)
            card_one[i].clear(true);
        card_one.clear(true);
        cdel.clear(true);
        return 1;
    }
    // printf("c [CE] scc cons: %d\n", scc);
    int res = card_elimination();
    for (int i = 0; i < mat.size(); i++)
        mat[i].clear(true);
    mat.clear(true);
    return res;
}

bool cmpvar(int x, int y) {
    return abs(x) < abs(y);
}

int simplify::cal_dup_val(int i) {
    for (int j = 0; j < clause[i].size(); j++) a[j] = clause[i][j];
    sort(a, a + clause[i].size(), cmpvar);
    int v = 0;
    for (int j = 0; j < clause[i].size(); j++)
        if (a[j] < 0) v |= (1 << j);
    return v;
}

int simplify::search_xors() {
    svec<int> xorsp;
    svec<bool> dup_table;
    for (int i = 1; i <= vars; i++) {
        seen[i] = 0;
        occurp[i].clear();
        occurn[i].clear();
    } 
    for (int i = 1; i <= clauses; i++) {
        abstract[i] = clause_delete[i] = nxtc[i] = 0;
        int l = clause[i].size();
        for (int j = 0; j < l; j++) {
            if (clause[i][j] > 0) occurp[clause[i][j]].push(i);
            else occurn[-clause[i][j]].push(i);
            abstract[i] |= 1 << (abs(clause[i][j]) & 31);
        }
    }
    for (int i = 1; i <= clauses; i++) {
        if (nxtc[i] || clause_delete[i]) continue;
        nxtc[i] = 1;
        int l = clause[i].size();
        if (l <= 2 || l > MAX_XOR) continue;
        int required_num = 1 << (l - 2), skip = 0, mino = clauses + 1, mino_id = 0;
        for (int j = 0; j < l; j++) {
            int idx = abs(clause[i][j]);
            if (occurp[idx].size() < required_num || occurn[idx].size() < required_num) {
                skip = 1; break;
            }
            if (occurp[idx].size() + occurn[idx].size() < mino) {
                mino = occurp[idx].size() + occurn[idx].size();
                mino_id = idx;
            }
        }
        if (skip) continue;
        xorsp.clear();
        xorsp.push(i);
        for (int j = 0; j < occurp[mino_id].size(); j++) {
            int o = occurp[mino_id][j];
            if (!clause_delete[o] && !nxtc[o] && clause[o].size() == l && abstract[o] == abstract[i])
                xorsp.push(o);
        }
        for (int j = 0; j < occurn[mino_id].size(); j++) {
            int o = occurn[mino_id][j];
            if (!clause_delete[o] && !nxtc[o] && clause[o].size() == l && abstract[o] == abstract[i])
                xorsp.push(o);
        }
        if (xorsp.size() < 2 * required_num) continue;

        int rhs[2] = {0, 0};
        for (int j = 0; j < l; j++)
            seen[abs(clause[i][j])] = i;
        dup_table.clear();
        dup_table.growTo(1 << MAX_XOR, false);
        
        for (int j = 0; j < xorsp.size(); j++) {
            int o = xorsp[j], dup_v;
            bool xor_sign = true;
            for (int k = 0; k < clause[o].size(); k++) {
                if (!seen[abs(clause[o][k])]) goto Next;
                if (clause[o][k] < 0) xor_sign = !xor_sign;
            }
            dup_v = cal_dup_val(o);
            if (dup_table[dup_v]) continue;
            dup_table[dup_v] = true;
            rhs[xor_sign]++;
            if (j) nxtc[o] = 1;
        Next:;
        }
        assert(rhs[0] <= 2 * required_num);
        assert(rhs[1] <= 2 * required_num);
        if (rhs[0] == 2 * required_num)
            xors.push(xorgate(i, 0, l));
        if (rhs[1] == 2 * required_num)
            xors.push(xorgate(i, 1, l));
    }
    return xors.size();
}

bool cmpxorgate(xorgate a, xorgate b) {
    return a.sz > b.sz;
}

int simplify::ecc_var() {
    scc_id.clear();
    scc_id.growTo(vars + 1, -1);
    scc.clear();
    //sort(xors.data, xors.data + xors.sz, cmpxorgate);
    svec<int> xids;

    for (int i = 0; i < xors.size(); i++) {
        int x = xors[i].c;
        xids.clear();
        for (int j = 0; j < clause[x].size(); j++)
            if (scc_id[abs(clause[x][j])] != -1)
                xids.push(scc_id[abs(clause[x][j])]);

        if (xids.size() == 0) {
            scc.push();
            for (int j = 0; j < clause[x].size(); j++) {
                scc_id[abs(clause[x][j])] = scc.size() - 1;
                scc[scc.size() - 1].push(abs(clause[x][j]));
            }
        }
        else if (xids.size() == 1) {
            int id = xids[0];
            for (int j = 0; j < clause[x].size(); j++) {
                if (scc_id[abs(clause[x][j])] == -1) {
                    scc_id[abs(clause[x][j])] = id;
                    scc[id].push(abs(clause[x][j]));
                }
            }
        }
        else {
            int id_max = -1; int sz_max = 0;
            for (int j = 0; j < xids.size(); j++)
                if (scc[xids[j]].size() > sz_max)
                    sz_max = scc[xids[j]].size(), id_max = xids[j];
            for (int j = 0; j < xids.size(); j++) {
                if (xids[j] != id_max) {
                    svec<int>& v = scc[xids[j]];
                    for (int k = 0; k < v.size(); k++) {
                        scc_id[v[k]] = id_max;
                        scc[id_max].push(v[k]);
                    }
                    v.clear();
                }
            }
            for (int j = 0; j < clause[x].size(); j++) {
                if (scc_id[abs(clause[x][j])] == -1) {
                    scc_id[abs(clause[x][j])] = id_max;
                    scc[id_max].push(abs(clause[x][j]));
                }
            }
        }
    }
    return scc.size();
}

int simplify::ecc_xor() {
    for (int i = 0; i < scc.size(); i++) seen[i] = -1;
    for (int i = 0; i < xors.size(); i++) {
        int id = scc_id[abs(clause[xors[i].c][0])];
        if (seen[id] == -1) xor_scc.push(), seen[id] = xor_scc.size() - 1;
        int id2 = seen[id];
        xor_scc[id2].push(i);
    }
    return xor_scc.size();
}

int simplify::gauss_elimination() {
    gauss_eli_unit = gauss_eli_binary = 0;
    svec<int> v2mzd(vars + 1, -1);
    svec<int> mzd2v;
    for (int i = 0; i < xor_scc.size(); i++) {
        if (xor_scc[i].size() == 1) continue;
        int id = scc_id[abs(clause[xors[xor_scc[i][0]].c][0])];
        assert(scc[id].size() > 3);
        if (scc[id].size() > 1e7 / xor_scc[i].size()) continue;
        mzd2v.clear();
        sort(scc[id].data, scc[id].data + scc[id].size(), cmpvar);
        for (int j = 0; j < scc[id].size(); j++) {
            assert(scc[id][j] > 0);
            assert(scc[id][j] <= vars);
            v2mzd[scc[id][j]] = j;
            mzd2v.push(scc[id][j]);
        }
        int cols = scc[id].size() + 1;
        mzd_t* mat = mzd_init(xor_scc[i].size(), cols);
        for (int row = 0; row < xor_scc[i].size(); row++) {
            int k = xors[xor_scc[i][row]].c;
            for (int j = 0; j < clause[k].size(); j++) 
                mzd_write_bit(mat, row, v2mzd[abs(clause[k][j])], 1);
            if (xors[xor_scc[i][row]].rhs) 
                mzd_write_bit(mat, row, cols - 1, 1); 
        }
        mzd_echelonize(mat, true);
        mzd_free(mat);
        for (int row = 0, rhs; row < xor_scc[i].size(); row++) {
            svec<int> ones;
            for (int col = 0; col < cols - 1; col++) 
                if (mzd_read_bit(mat, row, col)) {
                    if (ones.size() == 2) goto NextRow;
                    ones.push(mzd2v[col]);
                }
            
            rhs = mzd_read_bit(mat, row, cols - 1);
            if (ones.size() == 1) {
                ++gauss_eli_unit;
                clause.push();
                ++clauses;
                clause[clauses].push(ones[0] * (rhs ? 1 : -1));
            }
            else if (ones.size() == 2) {
                ++gauss_eli_binary;
                assert(clauses == clause.size() - 1);
                int p = ones[0], q = rhs ? ones[1] : -ones[1];
                clause.push();
                ++clauses;
                clause[clauses].push(p);
                clause[clauses].push(q);
                clause.push();
                ++clauses;
                clause[clauses].push(-p);
                clause[clauses].push(-q);
            }
            else if (rhs) {return false;}
        NextRow:;
        }
    }
    return true;
}

bool simplify::simplify_gauss() {
    int nxors = search_xors();
    // printf("c [GE] XORs: %d (time: 0.00)\n", nxors);
    if (!nxors) return true;
    int nvarscc = ecc_var();
    // printf("c [GE] VAR SCC: %d\n", nvarscc);
    int nxorscc = ecc_xor();
    // printf("c [GE] XOR SCCs: %d (time: 0.00)\n", nxorscc);
    int res = gauss_elimination();
    // printf("c [GE] unary xor: %d, bin xor: %d, bin added\n", gauss_eli_unit, gauss_eli_binary);
    // if (!res) {printf("c [GE] UNSAT\n");}
    xors.clear(true);
    scc_id.clear(true);
    for (int i = 0; i < scc.size(); i++)
        scc[i].clear(true);
    scc.clear(true);
    for (int i = 0; i < xor_scc.size(); i++)
        xor_scc[i].clear(true);
    xor_scc.clear(true);
    if (!res) return false;
    clause_delete.growTo(clauses + 1, 0);
    nxtc.growTo(clauses + 1, 0);
    return true;
}

bool simplify::res_is_empty(int x) {
    int op = occurp[x].size(), on = occurn[x].size();
    for (int i = 0; i < op; i++) {
        int o1 = occurp[x][i], l1 = clause[o1].size();
        if (clause_delete[o1]) continue;
        for (int j = 0; j < l1; j++)
            if (abs(clause[o1][j]) != x) resseen[abs(clause[o1][j])] = pnsign(clause[o1][j]);
        for (int j = 0; j < on; j++) {
            int o2 = occurn[x][j], l2 = clause[o2].size(), flag = 0;
            if (clause_delete[o2]) continue;
            for (int k = 0; k < l2; k++)
                if (abs(clause[o2][k]) != x && resseen[abs(clause[o2][k])] == -pnsign(clause[o2][k])) {
                    flag = 1; break;
                }
            if (!flag) {
                for (int j = 0; j < l1; j++)
                    resseen[abs(clause[o1][j])] = 0;
                return false;
            }
        }
        for (int j = 0; j < l1; j++)
            resseen[abs(clause[o1][j])] = 0;
    }
    return true; 
}

bool simplify::simplify_resolution() {
    
    for (int i = 1; i <= vars; i++) {
        occurn[i].clear();
        occurp[i].clear();
        resseen[i] = resseen[i + vars] = clean[i] = seen[i] = 0;
    }
    for (int i = 1; i <= clauses; i++) {
        int l = clause[i].size();
        clause_delete[i] = 0;
        for (int j = 0; j < l; j++)
            if (clause[i][j] > 0) occurp[abs(clause[i][j])].push(i);
            else occurn[abs(clause[i][j])].push(i);
    }
    for (int i = 1; i <= vars; i++)
        if (occurn[i].size() == 0 && occurp[i].size() == 0) clean[i] = 1;  

    int l = 1, r = 0;         
    for (int i = 1; i <= vars; i++) {
        int op = occurp[i].size(), on = occurn[i].size();
        if (op * on > op + on || clean[i]) continue;
        if (res_is_empty(i)) {
            q[++r] = i, clean[i] = 1;
        }
    }

    int now_turn = 0, seen_flag = 0;
    svec<int> vars;
    while (l <= r) {
        ++now_turn;
        for (int j = l; j <= r; j++) {
            int i = q[j];
            int op = occurp[i].size(), on = occurn[i].size();
            for (int j = 0; j < op; j++) clause_delete[occurp[i][j]] = 1;
            for (int j = 0; j < on; j++) clause_delete[occurn[i][j]] = 1;
        }
        int ll = l; l = r + 1;
        
        vars.clear();
        ++seen_flag;
        for (int u = ll; u <= r; u++) {
            int i = q[u];
            int op = occurp[i].size(), on = occurn[i].size();
            for (int j = 0; j < op; j++) {
                int o = occurp[i][j], l = clause[o].size();
                for (int k = 0; k < l; k++) {
                    int v = abs(clause[o][k]);
                    if (!clean[v] && seen[v] != seen_flag)
                        vars.push(v), seen[v] = seen_flag;
                }
            }
            for (int j = 0; j < on; j++) {
                int o = occurn[i][j], l = clause[o].size();
                for (int k = 0; k < l; k++) {
                    int v = abs(clause[o][k]);
                    if (!clean[v] && seen[v] != seen_flag)
                        vars.push(v), seen[v] = seen_flag;
                }
            }
        }
        for (int u = 0; u < vars.size(); u++) {
            int i = vars[u];
            int op = 0, on = 0;
            for (int j = 0; j < occurp[i].size(); j++) op += 1 - clause_delete[occurp[i][j]];
            for (int j = 0; j < occurn[i].size(); j++) on += 1 - clause_delete[occurn[i][j]];
            if (op * on > op + on) continue;
            if (res_is_empty(i)) {
                q[++r] = i, clean[i] = 1;
            }
        }
    }
    vars.clear(true);
    if (!r) return true;
    res_clauses = 0;
    res_clause.push();
    for (int i = 1; i <= clauses; i++) {
        if (!clause_delete[i]) continue;
        ++res_clauses;
        res_clause.push();
        int l = clause[i].size();
        for (int j = 0; j < l; j++) {
            res_clause[res_clauses].push(pnsign(clause[i][j]) * mapfrom[abs(clause[i][j])]);
        }
    }
    resolutions = r;
    resolution.push();
    for (int i = 1; i <= r; i++) {
        int v = mapfrom[q[i]];
        resolution.push(v);
        mapto[v] = 0, mapval[v] = -10;
    }
    update_var_clause_label();
    for (int i = 1; i <= orivars; i++) {
        if (mapto[i]) {
            mapto[i] = color[mapto[i]];
        }
    }
    return true;
}

void simplify::update_var_clause_label() {
    int remain_var = 0;
    for (int i = 1; i <= vars; i++) color[i] = 0;
    for (int i = 1; i <= clauses; i++) {
        if (clause_delete[i]) continue;
        int l = clause[i].size();
        for (int j = 0; j < l; j++) {
            if (color[abs(clause[i][j])] == 0) color[abs(clause[i][j])] = ++remain_var;       
        }
    }

    int id = 0;
    for (int i = 1; i <= clauses; i++) {
        if (clause_delete[i]) {clause[i].setsize(0); continue;}
        ++id;
        int l = clause[i].size();
        if (i == id) {
            for (int j = 0; j < l; j++)
                clause[id][j] = color[abs(clause[i][j])] * pnsign(clause[i][j]);    
            continue;
        }
        clause[id].setsize(0);
        for (int j = 0; j < l; j++)
            clause[id].push(color[abs(clause[i][j])] * pnsign(clause[i][j]));
    }
    // printf("c After simplify: vars: %d -> %d , clauses: %d -> %d ,\n", vars, remain_var, clauses, id);
    for (int i = id + 1; i <= clauses; i++) 
        clause[i].clear(true);
    for (int i = remain_var + 1; i <= vars; i++)
        occurp[i].clear(true), occurn[i].clear(true);
    clause.setsize(id + 1);
    vars = remain_var, clauses = id;
}

bool simplify::simplify_binary() { 
    C.clear();
    for (int i = 1; i <= clauses; i++) {
        int l = clause[i].size();
        for (int j = 0; j < l; j++)
            clause[i][j] = tolit(clause[i][j]);
    }
    nlit = 2 * vars + 2;
    int simplify = 1, turn = 0;
    for (int i = 1; i <= vars; i++) f[i] = i, val[i] = 1, varval[i] = color[i] = 0;
    for (int i = 1; i <= clauses; i++) clause_delete[i] = 0;

    int len = 0;
    for (int i = 1; i <= clauses; i++) {
        if (clause[i].size() != 2) continue;
        nxtc[++len] = i;
        ll id1 = mapv(clause[i][0], clause[i][1]),
           id2 = mapv(clause[i][1], clause[i][0]);
        C.insert(id1, i);
        C.insert(id2, i);
    }

    while (simplify) {
        simplify = 0;
        ++turn;        
        for (int k = 1; k <= len; k++) {
            int i = nxtc[k];
            if (clause[i].size() != 2 || clause_delete[i]) continue;
            ll id1 = mapv(reverse(clause[i][0]), reverse(clause[i][1])),
               id2 = mapv(clause[i][0], reverse(clause[i][1])),
               id3 = mapv(reverse(clause[i][0]), clause[i][1]);
            int r = C.get(id1, 0);
            if (r) {
                simplify = 1;
                clause_delete[r] = clause_delete[i] = 1;
                int fa = find(clause[i][0] >> 1), fb = find(clause[i][1] >> 1);
                int sig = sign(clause[i][0]) * sign(clause[i][1]) * (-1);
                //sig == 1 : a = b   -1 : a = -b
                if (fa != fb) {
                    if (fa < fb) {
                        f[fa] = fb;
                        val[fa] = sig / (val[clause[i][0] >> 1] * val[clause[i][1] >> 1]);
                        if (varval[fa])
                            varval[fb] = val[fa] * varval[fa];
                    }
                    else if (fa > fb) {
                        f[fb] = fa;
                        val[fb] = sig / (val[clause[i][0] >> 1] * val[clause[i][1] >> 1]);
                        if (varval[fb])
                            varval[fa] = val[fb] * varval[fb];
                    }
                }
                else {
                    if (sig != val[clause[i][0] >> 1] * val[clause[i][1] >> 1])
                        return false;
                }
            }
            int d1 = C.get(id2, 0);
            if (d1) {
                int v = clause[i][0] >> 1;
                if (varval[v] && varval[v] != sign(clause[i][0])) {
                    return false;
                }
                clause_delete[d1] = clause_delete[i] = 1;
                simplify = 1;
                varval[v] = sign(clause[i][0]);
            }
            int d2 = C.get(id3, 0);
            if (d2) {
                int v = clause[i][1] >> 1;
                if (varval[v] && varval[v] != sign(clause[i][1])) {
                    return false;
                }
                clause_delete[d2] = clause_delete[i] = 1;
                simplify = 1;
                varval[v] = sign(clause[i][1]); 
            }
        }

        for (int i = 1; i <= vars; i++) {
            int x = find(i);
            if (varval[i] && x != i) {
                if (varval[x]) {
                    if (varval[x] != varval[i] * val[i])
                        return false;
                }
                else varval[x] = varval[i] * val[i];
            }
        }
        for (int i = 1; i <= vars; i++) 
            if (varval[f[i]]) {
                if (varval[i]) {
                    if (varval[f[i]] != varval[i] * val[i])
                        return false;
                }
                else varval[i] = varval[f[i]] * val[i];
            }

        len = 0;

        for (int i = 1; i <= clauses; i++) {
            if (clause_delete[i]) continue;
            int l = clause[i].size(), oril = l;
            for (int j = 0; j < l; j++) {
                int fa = f[clause[i][j] >> 1];
                a[j] = tolit(sign(clause[i][j]) * val[clause[i][j] >> 1] * fa);
            }
            int t = 0;
            for (int j = 0; j < l; j++) {
                int x = varval[a[j] >> 1];
                if (x) {
                    int k = x * sign(a[j]);
                    if (k == 1) {
                        if (!clause_delete[i]) simplify = 1;
                        clause_delete[i] = 1, a[t++] = a[j];
                    }
                }
                else a[t++] = a[j];
            }
            if (t == 0) return false;
            if (t != l) simplify = 1, l = t;
            t = 0;
            for (int j = 0; j < l; j++) {
                if (resseen[a[j]] == i) continue;
                resseen[a[j]] = i, a[t++] = a[j];
            }
            if (t != l) simplify = 1, l = t;
            for (int j = 0; j < l; j++)
                if (resseen[reverse(a[j])] == i && !clause_delete[i])
                    clause_delete[i] = 1, simplify = 1;
            
            for (int j = 0; j < l; j++) resseen[a[j]] = 0;
                
            if (l == 1) {
                if (sign(a[0]) * varval[a[0] >> 1] == -1) return false;
                varval[a[0] >> 1] = sign(a[0]);
                simplify = 1;
            }
            if (!clause_delete[i] && l == 2 && oril != 2) {
                nxtc[++len] = i;
                ll id1 = mapv(a[0], a[1]),
                   id2 = mapv(a[1], a[0]);
                C.insert(id1, i);
                C.insert(id2, i);
            }
            else if (!clause_delete[i] && l == 2 &&  oril == 2) {
                if (a[0] == clause[i][0] && a[1] == clause[i][1]) ;
                else if (a[1] == clause[i][0] && a[0] == clause[i][1]) ;
                else {
                    nxtc[++len] = i;
                    ll id1 = mapv(a[0], a[1]),
                       id2 = mapv(a[1], a[0]);
                    C.insert(id1, i);
                    C.insert(id2, i);
                }
            }
            clause[i].clear();
            for (int j = 0; j < l; j++)
                clause[i].push(a[j]);
        }

        for (int i = 1; i <= vars; i++) {
            int x = find(i);
            if (varval[i] && x != i) {
                if (varval[x]) {
                    if (varval[x] != varval[i] * val[i])
                        return false;
                }
                else varval[x] = varval[i] * val[i];
            }
        }
        for (int i = 1; i <= vars; i++) 
            if (varval[f[i]]) {
                if (varval[i]) {
                    if (varval[f[i]] != varval[i] * val[i])
                        return false;
                }
                else varval[i] = varval[f[i]] * val[i];
            }
    }

    for (int i = 1; i <= clauses; i++) {
        if (clause_delete[i]) continue;
        int l = clause[i].size();
        for (int j = 0; j < l; j++) {
            clause[i][j] = sign(clause[i][j]) * (clause[i][j] >> 1);
        }
    }
    update_var_clause_label();
    for (int i = 1; i <= orivars; i++) {
        if (mapval[i]) {
            continue;
        }
        int v = mapto[i], fa = find(v);
        if (varval[v] || varval[fa]) {
            mapval[i] = varval[v];
            mapto[i] = 0;
        }
        else if (color[fa]) mapto[i] = color[fa] * val[v];
        else mapval[i] = val[v], mapto[i] = 0;
    }
    return true;
}

bool simplify::simplify_easy_clause() {
    for (int i = 1; i <= vars; i++) {
        varval[i] = 0;
        occurp[i].clear();
        occurn[i].clear();
        resseen[i] = resseen[i + vars] = 0;
    }
    for (int i = 1; i <= clauses; i++) clause_delete[i] = 0;
    int head = 1, tail = 0;
    for (int i = 1; i <= clauses; i++) {
        int l = clause[i].size(), t = 0;
        for (int j = 0; j < l; j++) {
            int lit = TOLIT(clause[i][j]);
            if (resseen[lit] == i) continue;
            if (resseen[NEG(lit)] == i) {clause_delete[i] = 1; break;}
            clause[i][t++] = clause[i][j];
            resseen[lit] = i;
        }
        if (clause_delete[i]) continue;
        clause[i].setsize(t);
        for (int j = 0; j < t; j++) 
            if (clause[i][j] > 0) occurp[clause[i][j]].push(i);
            else occurn[-clause[i][j]].push(i);
        if (t == 0) return false;
        if (t == 1) {
            int lit = clause[i][0];
            clause_delete[i] = 1;
            if (varval[abs(lit)]) {
                if (varval[abs(lit)] == pnsign(lit)) continue;
                else return false;
            }
            varval[abs(lit)] = pnsign(lit); 
            q[++tail] = abs(lit); 
        }
    }
    for (int i = 1; i <= vars + vars; i++) resseen[i] = 0;
    while (head <= tail) {
        int x = q[head++];
        if (varval[x] == 1) {
            for (int i = 0; i < occurp[x].size(); i++)
                clause_delete[occurp[x][i]] = 1;
            for (int i = 0; i < occurn[x].size(); i++) {
                int o = occurn[x][i], t = 0;
                if (clause_delete[o]) continue;
                for (int j = 0; j < clause[o].size(); j++) {
                    if (varval[abs(clause[o][j])] == pnsign(clause[o][j])) {
                        clause_delete[o] = 1; break;
                    }
                    if (varval[abs(clause[o][j])] == -pnsign(clause[o][j])) continue;
                    clause[o][t++] = clause[o][j];
                }
                if (clause_delete[o]) continue;
                clause[o].setsize(t);
                if (t == 0) return false;
                if (t == 1) {
                    int lit = clause[o][0];
                    clause_delete[o] = 1;
                    if (varval[abs(lit)]) {
                        if (varval[abs(lit)] == pnsign(lit)) continue;
                        else return false;
                    }
                    varval[abs(lit)] = pnsign(lit); 
                    q[++tail] = abs(lit); 
                }
            }
        }
        else {
            for (int i = 0; i < occurn[x].size(); i++)
                clause_delete[occurn[x][i]] = 1;
            for (int i = 0; i < occurp[x].size(); i++) {
                int o = occurp[x][i], t = 0;
                if (clause_delete[o]) continue;
                for (int j = 0; j < clause[o].size(); j++) {
                    if (varval[abs(clause[o][j])] == pnsign(clause[o][j])) {
                        clause_delete[o] = 1; break;
                    }
                    if (varval[abs(clause[o][j])] == -pnsign(clause[o][j])) continue;
                    clause[o][t++] = clause[o][j];
                }
                if (clause_delete[o]) continue;
                clause[o].setsize(t);
                if (t == 0) return false;
                if (t == 1) {
                    int lit = clause[o][0];
                    clause_delete[o] = 1;
                    if (varval[abs(lit)]) {
                        if (varval[abs(lit)] == pnsign(lit)) continue;
                        else return false;
                    }
                    varval[abs(lit)] = pnsign(lit); 
                    q[++tail] = abs(lit); 
                }
            }
        }
    }
    update_var_clause_label();

    for (int i = 1; i <= tail; i++) {
        int v = q[i];
        mapval[v] = varval[v];
    }
    mapfrom = new int[vars + 1];
    for (int i = 1; i <= vars; i++) mapfrom[i] = 0;
    for (int i = 1; i <= orivars; i++) {
        if (color[i])
            mapto[i] = color[i], mapfrom[color[i]] = i;
        else if (!mapval[i]) // not in unit queue, then it is no use var
            mapto[i] = 0, mapval[i] = 1;
        else
            mapto[i] = 0;
    }
    return true;
}

void simplify::print_complete_model() {
    int r = 0;
    for (int i = 1; i <= orivars; i++) 
        if (!mapto[i]) {
            if (!mapval[i]);
            else if (abs(mapval[i]) != 1) mapval[i] = 0, ++r;
        }
    if (r) { 
        occurp = new svec<int>[orivars + 1];
        occurn = new svec<int>[orivars + 1];   
        for (int i = 1; i <= orivars; i++) {
            occurp[i].clear(), occurn[i].clear();
        }
        svec<int> clause_state;
        clause_state.growTo(res_clauses + 1, 0);
        for (int i = 1; i <= res_clauses; i++) {
            int satisify = 0;
            for (int j = 0; j < res_clause[i].size(); j++) {
                int v = res_clause[i][j];
                if (v > 0) occurp[v].push(i);
                else occurn[-v].push(i);
                if (pnsign(v) * mapval[abs(v)] == 1) satisify = 1;
                if (!mapval[abs(v)]) ++clause_state[i];
            }
            if (satisify) clause_state[i] = -1;
        }
        for (int ii = resolutions; ii >= 1; ii--) {
            int v = resolution[ii];
            //attempt 1
            int assign = 1;
            for (int i = 0; i < occurn[v].size(); i++) {
                int o = occurn[v][i];
                if (clause_state[o] != -1 && clause_state[o] <= 1) {assign = 0; break;}
            }
            if (assign == 1) {
                mapval[v] = 1;
                for (int i = 0; i < occurn[v].size(); i++) {
                    int o = occurn[v][i];
                    if (clause_state[o] != -1) clause_state[o]--;
                } 
                for (int i = 0; i < occurp[v].size(); i++) 
                    clause_state[occurp[v][i]] = -1;
                continue;
            }
            //attempt -1
            assign = -1;
            for (int i = 0; i < occurp[v].size(); i++) {
                int o = occurp[v][i];
                if (clause_state[o] != -1 && clause_state[o] <= 1) {assign = 0; break;}
            }
            if (assign == -1) {
                mapval[v] = -1;
                for (int i = 0; i < occurp[v].size(); i++) {
                    int o = occurp[v][i];
                    if (clause_state[o] != -1) clause_state[o]--;
                } 
                for (int i = 0; i < occurn[v].size(); i++) 
                    clause_state[occurn[v][i]] = -1;
                continue;
            }
        }
        clause_state.clear(true);
        for (int i = 1; i <= orivars; i++) {
            occurp[i].clear(true), occurn[i].clear(true);
        }
        delete []occurp;
        delete []occurn;
        res_clause.clear(true);
        resolution.clear(true);
    }  
}