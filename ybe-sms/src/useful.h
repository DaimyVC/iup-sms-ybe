#ifndef USEFUL_H
#define USEFUL_H


#include "domains.h"
#include <algorithm>
#include <utility>
#include <vector>
#include <iostream>
#include <numeric>
#include <string>
#include <string.h>
#include <cassert>
#include <fstream>
#include <sstream>
#include <unordered_set>
#include <chrono>

#include <unordered_map>
#include <boost/icl/interval_set.hpp>

using namespace std;
using namespace chrono;

typedef int lit_t;
typedef vector<lit_t> clause_t;
typedef vector<clause_t> cnf_t;
typedef vector<vector<vector<lit_t>>> matrixLits_t;
typedef vector<vector<vector<vector<lit_t>>>> ybeLits_t;

void printCnf(cnf_t *cnf);

#define PRINT_CURRENT_LINE                            \
    printf("Line %d, file %s\n", __LINE__, __FILE__); \
    fflush(stdout);

#define EXIT_UNWANTED_STATE                                                          \
    {                                                                                \
        printf("Error: unexpected state at line %d, file %s\n", __LINE__, __FILE__); \
        exit(EXIT_FAILURE);                                                          \
    }

typedef enum {
    True_t=1,
    False_t=0,
    Unknown_t=-1
} truth_vals;

typedef struct cycle_set_t{
    std::vector<vector<int>> matrix;
    std::vector<vector<vector<truth_vals>>> assignments;
    std::vector<vector<vector<int>>> cycset_lits;
    std::vector<vector<bitdomain_t>> bitdomains;

    cycle_set_t(int problem_size, std::vector<vector<vector<int>>> lits){
        cycset_lits=lits;
        assignments=vector<vector<vector<truth_vals>>>(problem_size, vector<vector<truth_vals>>(problem_size, vector<truth_vals>(problem_size, Unknown_t)));
        matrix=vector<vector<int>>(problem_size, vector<int>(problem_size, -1));
        bitdomains=vector<vector<bitdomain_t>>(problem_size,vector<bitdomain_t>(problem_size,bitdomain_t(problem_size,true)));
    }

    cycle_set_t() = default;
} cycle_set_t;

class pperm_common
{
public:
    virtual ~pperm_common(){}
    virtual shared_ptr<pperm_common> copyPerm() { EXIT_UNWANTED_STATE };
    virtual int permOf(int p) { EXIT_UNWANTED_STATE };
    virtual vector<int> options(int p) { EXIT_UNWANTED_STATE };
    virtual vector<int> invOptions(int p) { EXIT_UNWANTED_STATE };
    virtual int invPermOf(int p) { EXIT_UNWANTED_STATE };
    virtual bool fixed(int p) { EXIT_UNWANTED_STATE };
    virtual bool fix(int p, int pp) { EXIT_UNWANTED_STATE };
    virtual void print() { EXIT_UNWANTED_STATE };
    virtual bool fullDefined() { EXIT_UNWANTED_STATE };
    virtual vector<int> getPerm() { EXIT_UNWANTED_STATE }; 
};

class pperm_plain : public pperm_common
{
public:
    std::vector<int> element;
    std::vector<bool> part;
    shared_ptr<pperm_common> copyPerm();
    
    int permOf(int p);
    vector<int> options(int p);
    vector<int> invOptions(int p);
    int invPermOf(int p);
    bool fixed(int p);
    bool fix(int p, int pp);
    void print();
    bool fullDefined();
    vector<int> getPerm();
    pperm_plain(std::vector<int> perm);
    pperm_plain();
    ~pperm_plain();
};

class pperm_bit : public pperm_common
{
public:
    bitdomains2_t info;
    shared_ptr<pperm_common> copyPerm();

    int permOf(int p);
    vector<int> options(int p);
    vector<int> invOptions(int p);
    int invPermOf(int p);
    bool fixed(int p);
    bool fix(int p, int pp);
    void print();
    bool fullDefined();
    vector<int> getPerm();
    pperm_bit(vector<int> perm);
    pperm_bit();
    ~pperm_bit();
};

typedef struct cyclePerm_t{
    std::vector<int> element;
    std::vector<int> part;

    cyclePerm_t(std::vector<int> perm);
    cyclePerm_t();
    int permOf(int p);
    int invPermOf(int p);
    vector<int> cycle(int el);
    void print();
} cyclePerm_t;

vector<vector<int>> permToCyclePerm(vector<int> &perm);
void printCycleSet(const cycle_set_t &cycset);
void fprintCycleSet(FILE *stream, const cycle_set_t &cycset);
void printPartiallyDefinedCycleSet(const cycle_set_t &cycset);
void printDomains(const cycle_set_t &cycset);
void printAssignments(const cycle_set_t &cycset);
void part(int n, vector<int>& v, int level, vector<vector<int>>& parts);
void makeDiagonals(vector<vector<int>>& parts, vector<vector<int>>& permutations);
void cycleToParts(vector<vector<int>> &perm, vector<int> &ord, vector<bool> &part);
vector<pperm_bit> combinePerms(vector<pperm_bit> &validOptions);
#endif