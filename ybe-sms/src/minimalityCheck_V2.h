#include "useful.h"
#include<list>

class LimitReachedException
{
};

/**
 * Check if cycle set is minimal and add a clause if this is not the case.
 * Throws std::vector<signed_edge_t> if current partially defined graph is not minimal
 * Throws LimitReachedException if cutoff limit is reached
 */

void checkMinimality_v2(cycle_set_t &cycset);

int smallerOrEqualSymms(cycle_set_t &cycset, list<vector<int>> &fixingPerms, vector<int> &perm, int i, int j);

int minimalityCheck(cycle_set_t &cycset, list<vector<int>> &fixingPerms, vector<int> &perm, int r, int c, int res);

void addClauses(cycle_set_t &cycset, vector<int> &perm, int r, int c);