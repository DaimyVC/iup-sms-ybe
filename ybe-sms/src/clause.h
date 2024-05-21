#include "useful.h"
#include "global.h"

void encodeEntries(cnf_t *cnf, int &nextFree, vector<vector<vector<lit_t>>> &cycset_lits);
void YBEClauses(cnf_t *cnf, int &nextFree, vector<vector<vector<lit_t>>> &cycset_lits, vector<vector<lit_t>> &ybe_left_lits, vector<vector<lit_t>> &ybe_right_lits, vector<vector<lit_t>> &ybe_lits);
void encodeEntries(cnf_t *cnf, vector<int> d, int &nextFree, vector<vector<vector<lit_t>>> &cycset_lits);
void encodeOrder(cnf_t *cnf, vector<int> d, int &nextFree, vector<vector<vector<lit_t>>> &cycset_lits_ord, vector<vector<vector<lit_t>>> &cycset_lits);
void YBEClauses(cnf_t *cnf, vector<int> d, int &nextFree, vector<vector<vector<lit_t>>> &cycset_lits, vector<vector<lit_t>> &ybe_left_lits, vector<vector<lit_t>> &ybe_right_lits, vector<vector<lit_t>> &ybe_lits);
void atLeastOne(cnf_t *cnf, vector<int> alo);
void atMostOne(cnf_t *cnf, vector<int> alo);
void exactlyOne(cnf_t *cnf, vector<int> eo,int &nextFree);
pair<int,cnf_t> commanderEncoding(vector<int> amo, int &nextFree);
void fixFirstRow(cnf_t *cnf, vector<vector<vector<lit_t>>> &cycset_lits, vector<int> firstRow);
void unfixFirstRow(cnf_t *cnf, vector<vector<vector<lit_t>>> &cycset_lits, vector<int> firstRow);
void YBEClausesNew(cnf_t *cnf, int &nextFree, vector<vector<vector<lit_t>>> &cycset_lits);
void YBEClausesNew(cnf_t *cnf, int &nextFree, vector<vector<vector<lit_t>>> &cycset_lits, vector<int> diag);
