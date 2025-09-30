#ifndef USEFUL_H
#define USEFUL_H


#include "domains.h"
#include <algorithm>
#include <vector>
#include <iostream>
#include <cstring>
#include <fstream>
#include <chrono>
#include <memory>
#include <map>

using namespace std;
using namespace chrono;

typedef int lit_t;
typedef vector<lit_t> clause_t;
typedef vector<clause_t> cnf_t;
typedef vector<vector<vector<lit_t>>> matrixLits_t;
typedef vector<vector<vector<vector<lit_t>>>> ybeLits_t;

void printCnf(cnf_t *cnf, FILE* out);

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

typedef struct order_t {
    vector<pair<int,int>> orderedCells=vector<pair<int,int>>();
    vector<int> orderedLits=vector<int>();
} order_t;

typedef struct cycle_set_t{
    std::vector<vector<int>> matrix;
    std::vector<vector<vector<truth_vals>>> assignments;
    std::vector<vector<vector<int>>> cycset_lits;
    std::vector<vector<bitdomain_t>> bitdomains;

    cycle_set_t(int problem_size, const std::vector<vector<vector<int>>> &lits){
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
    virtual ~pperm_common()= default;
    virtual shared_ptr<pperm_common> copyPerm() { EXIT_UNWANTED_STATE };
    virtual int permOf(int /*p*/) { EXIT_UNWANTED_STATE };
    virtual vector<int> options(int /*p*/) { EXIT_UNWANTED_STATE };
    virtual vector<int> invOptions(int /*p*/) { EXIT_UNWANTED_STATE };
    virtual int invPermOf(int /*p*/) { EXIT_UNWANTED_STATE };
    virtual bool fixed(int /*p*/) { EXIT_UNWANTED_STATE };
    virtual bool fix(int /*p*/, int /*pp*/) { EXIT_UNWANTED_STATE };
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
    pperm_plain(const std::vector<int>& perm);
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
    pperm_bit(const vector<int>& perm);
    pperm_bit();
    ~pperm_bit();
};

typedef struct cyclePerm_t{
    std::vector<int> element;
    std::vector<int> part;
    std::vector<int> diag;
    int sz;
    cyclePerm_t(const std::vector<int>& perm);
    cyclePerm_t(const std::vector<vector<int>>& perm);
    cyclePerm_t();
    int permOf(int p);
    int invPermOf(int p);
    vector<int> cycle(int el);
    void print();
} cyclePerm_t;

typedef struct broken{
    cycle_set_t cycset;
    int r;
    int c;
    broken(cycle_set_t cycset, int r, int c);
}broken;

typedef struct breakCounter{
    std::map<vector<int>,int> counts;
    std::map<vector<int>,vector<broken>> brokens;
    void addPerm(vector<int> p, cycle_set_t cycset, int r, int c);
    void exportCounts(int n);
    breakCounter();
}breakCounter;

vector<vector<int>> permToCyclePerm(const vector<int> &perm);
void printCycleSet(const cycle_set_t &cycset);
void fprintCycleSet(FILE *stream, const cycle_set_t &cycset);
void fprintPermCycleSet(FILE *stream, const cycle_set_t &cycset, vector<int> perm);
void printPartiallyDefinedCycleSet(const cycle_set_t &cycset);
void printDomains(const cycle_set_t &cycset);
void printAssignments(const cycle_set_t &cycset);
void part(int n, vector<int>& v, int level, vector<vector<int>>& parts);
void makeDiagonals(vector<vector<int>>& parts, vector<vector<int>>& permutations);
void cycleToParts(vector<vector<int>> &perm, vector<int> &ord, vector<bool> &part);
vector<pperm_bit> combinePerms(vector<pperm_bit> &validOptions);
vector<int> reduceDiag(vector<int> ogDiag);
#endif