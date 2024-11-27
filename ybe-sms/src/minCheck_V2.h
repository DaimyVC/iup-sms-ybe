#include "useful.h"
#include<queue>
#include "minCheckCommon.h"
#include "incr_minCheck.h"

/**
 * Check if cycle set is minimal and add a clause if this is not the case.
 * Throws std::vector<signed_edge_t> if current partially defined graph is not minimal
 * Throws LimitReachedException if cutoff limit is reached
 */

class MinCheck_V2 : public MinCheckCommon
{
public:
    //MinCheck_V2(cycle_set_t cycset, vector<vector<vector<lit_t>>> cycset_lits);
    MinCheck_V2();
    MinCheck_V2(vector<int> diag, vector<vector<vector<lit_t>>> cycset_lits);
    void checkMinimality(shared_ptr<pperm_common> perm, int r, int d);
    void MinCheck(cycle_set_t cycset);


private:
    void extendPerm(shared_ptr<pperm_common> perm);
    void filterOptions(shared_ptr<pperm_common> perm, vector<int> &options, int r, vector<shared_ptr<pperm_common>> &options_prop);
    void filterOptions2(shared_ptr<pperm_common> perm, vector<int> &options, int r, vector<shared_ptr<pperm_common>> &options_prop);
    bool propagateDecision(shared_ptr<pperm_common> perm, int r);
    bool fixAndPropagate(shared_ptr<pperm_common> perm, int i, int j);
    shared_ptr<pperm_common> inverseUnkown(shared_ptr<pperm_common> perm, int i, int j);
    IncrMinCheck incrMinChecker;
};