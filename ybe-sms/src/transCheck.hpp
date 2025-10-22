#ifndef TRANS_CHECK_H
#define TRANS_CHECK_H

#include "useful.h"
#include <set>

class TransitivityCheck
{
public:
    bool TransCheck(cycle_set_t cycset);
    void preventDecomposable(cycle_set_t cycset);

protected:
    cycle_set_t cycset;
    cyclePerm_t diag;

    vector<vector<int>> constructOrbits();
    vector<int> constructOrbit(int el);
};

#endif