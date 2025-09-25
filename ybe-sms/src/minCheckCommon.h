#ifndef MIN_CHECK_COMMON_H
#define MIN_CHECK_COMMON_H

#include "useful.h"

class LimitReachedException
{
};

class MinCheckCommon
{
public:
    bool preCheck(cycle_set_t &cycset);
    virtual void MinCheck(cycle_set_t /*cycset*/) { EXIT_UNWANTED_STATE };
    bool final;
    bool complete;

protected:
    cycle_set_t cycset;
    vector<vector<vector<lit_t>>> cycset_lits;
    cyclePerm_t diag;
    shared_ptr<pperm_common> initialPart;
    bool diagIsId;
    int its;
    bool permIsId(const vector<int> &perm);
    int permFullyDefinedCheck(vector<int> &perm, int i, int j);
    void addClauses(const vector<int> &perm, int r, int c);
    void addClausesShort(const vector<int> &perm, int r, int c);
    void toClause(vector<bitdomains2_t> &lits, vector<int> &cls);
    void addToClause(int r, int c, int lit, vector<bitdomains2_t> &lits, bool neg);
    void addClauses(const vector<int> &perm, int r, int c, bool old);
};

#endif