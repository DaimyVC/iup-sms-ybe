#ifndef DOMAIN_H
#define DOMAIN_H

#include <vector>

using namespace std;

typedef struct bitdomain_t{
    vector<bool> dom;
    int size;
    int firstel;
    int numTrue;
    bitdomain_t();
    bitdomain_t(int n,bool init);
    void set(int n);
    void reset(int n);
    void set();
    void reset();
    bool none();
    vector<int> options();
    void print();
} bitdomain_t;

typedef struct bitdomains2_t{
    vector<int> dom;
    int chunk;
    bitdomains2_t();
    bitdomains2_t(bool init);
    ~bitdomains2_t();

    int get(int idx) ;
    bool get(int idx, int e) ;

    void set();
    void reset();

    int firstel(int e) ;
    int numtrue(int e) ;
    void set(int e,int n);
    void reset(int e,int n);
    void set(int e);
    void reset(int e);
    bool none(int e);
    vector<int> options(int e);

    void print();
} bitdomains2_t;

typedef struct bitdomains3_t{
    vector<int> dom;
    int chunkr;
    int chunkc;
    bitdomains3_t();
    bitdomains3_t(bool init);
    ~bitdomains3_t();

    int get(int r, int c);
    bool get(int r, int c, int e) ;

    void set();
    void reset();

    int firstel(int r, int c) ;
    int numtrue(int r, int c) ;
    void set(int r, int c,int n);
    void reset(int r, int c,int n);
    void set(int r, int c);
    void reset(int r, int c);
    bool none(int r, int c);
    vector<int> options(int r, int c) ;
    void print();
} bitdomains3_t;

#endif