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
    IncrMinCheck(cyclePerm_t &diag, shared_ptr<pperm_common> initialPart, bool isId);
    bool solvePartial(cycle_set_t &assump);
    bool solveComplete(cycle_set_t &assump);
    bool solve();
    vector<int> extractPartialPerm();
    vector<int> extractCompletePerm();

private:
    cyclePerm_t diag;
    shared_ptr<pperm_common> initialPart;
    bool isId;

    CaDiCaL::Solver *partialSolver;
    vector<vector<int>> part_lit2entry;
    int part_highestOgCycsetVar;
    int part_highestPermCycsetVar;
    int part_highestPermVar;
    cnf_t part_cnf;
    int part_nextFreeVariable = 1;
    vector<vector<vector<lit_t>>> part_cycset_lits = vector<vector<vector<lit_t>>>(problem_size, vector<vector<lit_t>>(problem_size, vector<lit_t>(problem_size, 0)));
    vector<vector<vector<lit_t>>> part_perm_cycset_lits = vector<vector<vector<lit_t>>>(problem_size, vector<vector<lit_t>>(problem_size, vector<lit_t>(problem_size, 0)));
    vector<vector<lit_t>> part_perm_lits = vector<vector<lit_t>>(problem_size, vector<lit_t>(problem_size, 0));
    
    CaDiCaL::Solver *completeSolver;
    vector<vector<int>> comp_lit2entry;
    int comp_highestOgCycsetVar;
    int comp_highestPermCycsetVar;
    int comp_highestPermVar;
    cnf_t comp_cnf;
    int comp_nextFreeVariable = 1;
    vector<vector<vector<lit_t>>> comp_cycset_lits = vector<vector<vector<lit_t>>>(problem_size, vector<vector<lit_t>>(problem_size, vector<lit_t>(problem_size, 0)));
    vector<vector<vector<lit_t>>> comp_perm_cycset_lits = vector<vector<vector<lit_t>>>(problem_size, vector<vector<lit_t>>(problem_size, vector<lit_t>(problem_size, 0)));
    vector<vector<lit_t>> comp_perm_lits = vector<vector<lit_t>>(problem_size, vector<lit_t>(problem_size, 0));
};
