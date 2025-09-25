#include "useful.h"
#include "solveCadicalClass.hpp"

class MinCheckCNF;

class IncrMinCheck
{
public:
    IncrMinCheck();
    IncrMinCheck(cyclePerm_t &diag, const shared_ptr<pperm_common>& initialPart, bool isId);
    bool solvePartial(cycle_set_t &assump);
    bool solveComplete(const cycle_set_t &assump);
    bool solve();
    vector<int> extractPartialPerm();
    vector<int> extractCompletePerm();
    friend class MinCheckCNF;

private:
    cyclePerm_t diag;
    shared_ptr<pperm_common> initialPart;
    bool isId{};

    CaDiCaL::Solver *partialSolver{};
    vector<vector<int>> part_lit2entry;
    int part_highestOgCycsetVar{};
    int part_highestPermCycsetVar{};
    int part_highestPermVar{};
    cnf_t part_cnf;
    int part_nextFreeVariable = 1;
    vector<vector<vector<lit_t>>> part_cycset_lits = vector<vector<vector<lit_t>>>(problem_size, vector<vector<lit_t>>(problem_size, vector<lit_t>(problem_size, 0)));
    vector<vector<vector<lit_t>>> part_greater_lits = vector<vector<vector<lit_t>>>(problem_size, vector<vector<lit_t>>(problem_size, vector<lit_t>(problem_size, 0)));
    vector<vector<vector<lit_t>>> part_perm_cycset_lits = vector<vector<vector<lit_t>>>(problem_size, vector<vector<lit_t>>(problem_size, vector<lit_t>(problem_size, 0)));
    vector<vector<lit_t>> part_perm_lits = vector<vector<lit_t>>(problem_size, vector<lit_t>(problem_size, 0));
    
    CaDiCaL::Solver *completeSolver{};
    vector<vector<int>> comp_lit2entry;
    int comp_highestOgCycsetVar{};
    int comp_highestPermCycsetVar{};
    int comp_highestPermVar{};
    cnf_t comp_cnf;
    int comp_nextFreeVariable = 1;

    vector<vector<vector<lit_t>>> complete_cycset_lits;
    vector<vector<vector<lit_t>>> complete_perm_cycset_lits;
    vector<vector<lit_t>> complete_perm_lits;
    CaDiCaL::Solver *comp_Solver{};
};
