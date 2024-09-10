//solver
//assumptions
//addassump
//removeassump?
//mincheck (solve, if sat extract perm, if unsat -> minimal)
//constructCNF

#include "useful.h"
#include "global.h"
#include "clause.h"
#include "solveGeneral.hpp"
#include "solveCadicalClass.hpp"

class IncrMinCheck
{
public:
    IncrMinCheck();
    bool solve(cycle_set_t &assump);
    bool solve();
    vector<vector<vector<lit_t>>> cycset_lits = vector<vector<vector<lit_t>>>(problem_size, vector<vector<lit_t>>(problem_size, vector<lit_t>(problem_size, 0)));
    vector<int> extractPerm();

private:
    CaDiCaL::Solver *solver;
    vector<vector<int>> lit2entry;
    int highestOgCycsetVar;
    int highestPermCycsetVar;
    int highestPermVar;
    cnf_t cnf;
    int nextFreeVariable = 1;
    vector<vector<vector<lit_t>>> perm_cycset_lits = vector<vector<vector<lit_t>>>(problem_size, vector<vector<lit_t>>(problem_size, vector<lit_t>(problem_size, 0)));
    vector<vector<lit_t>> perm_lits = vector<vector<lit_t>>(problem_size, vector<lit_t>(problem_size, 0));

};
