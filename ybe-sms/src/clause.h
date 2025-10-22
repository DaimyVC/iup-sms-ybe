#include "useful.h"

void encodeEntries(cnf_t *cnf, const vector<int> &diag, int &nextFree, matrixLits_t &cycset_lits);
void encodeOrder(cnf_t *cnf, const vector<int> &d, int &nextFree, matrixLits_t &cycset_lits_ord, const matrixLits_t &cycset_lits);
void atLeastOne(cnf_t *cnf, const vector<int>& alo);
void atMostOne(cnf_t *cnf, const vector<int> &alo);
void exactlyOne(cnf_t *cnf, const vector<int>& eo,int &nextFree);
pair<int,cnf_t> commanderEncoding(vector<int> amo, int &nextFree);
void YBEClauses(cnf_t *cnf, int &nextFree, const matrixLits_t &cycset_lits, const vector<int> &diag);
void findWitness(cnf_t *cnf, int &nextFree, matrixLits_t &cycset_lits, matrixLits_t &perm_cycset_lits, vector<vector<lit_t>> &perm_lits,cyclePerm_t &diag, const shared_ptr<pperm_common>& initialPart, bool isId, order_t order);
void findPartialWitness(cnf_t *cnf, int &nextFree, matrixLits_t &cycset_lits, matrixLits_t &perm_cycset_lits, vector<vector<lit_t>> &perm_lits,matrixLits_t &larger,cyclePerm_t &diag, const shared_ptr<pperm_common>& initialPart, bool isId, order_t order);
//void findPartialWitness2(cnf_t *cnf, int &nextFree, matrixLits_t &cycset_lits, matrixLits_t &perm_cycset_lits, vector<vector<lit_t>> &perm_lits,matrixLits_t &larger,cyclePerm_t &diag, const shared_ptr<pperm_common>& initialPart, bool isId);
void addStaticSBP(cnf_t *cnf, int &nextFree, matrixLits_t &cycset_lits, matrixLits_t &geq_lits, vector<int> &diag, order_t order, vector<int> breakPerm, int lim, bool old);
void enforceNoFixedEntries(cnf_t *cnf, const vector<int> &d, const matrixLits_t &cycset_lits);
