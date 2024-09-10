#include "useful.h"
#include "global.h"

void encodeEntries(cnf_t *cnf, int &nextFree, matrixLits_t &cycset_lits);
void encodeEntries(cnf_t *cnf, vector<int> d, int &nextFree, matrixLits_t &cycset_lits);
void encodeOrder(cnf_t *cnf, vector<int> d, int &nextFree, matrixLits_t &cycset_lits_ord, matrixLits_t &cycset_lits);
void atLeastOne(cnf_t *cnf, vector<int> alo);
void atMostOne(cnf_t *cnf, vector<int> alo);
void exactlyOne(cnf_t *cnf, vector<int> eo,int &nextFree);
pair<int,cnf_t> commanderEncoding(vector<int> amo, int &nextFree);
void fixFirstRows(cnf_t *cnf, matrixLits_t &cycset_lits, vector<int> firstRow, int n);
void unfixFirstRows(cnf_t *cnf, matrixLits_t &cycset_lits, vector<int> firstRow, int n);
void YBEClausesNew(cnf_t *cnf, int &nextFree, matrixLits_t &cycset_lits);
void YBEClausesNew(cnf_t *cnf, int &nextFree, matrixLits_t &cycset_lits, vector<int> diag);
void findWitness(cnf_t *cnf, int &nextFree, matrixLits_t &cycset_lits, matrixLits_t &perm_cycset_lits, vector<vector<lit_t>> &perm_lits);
