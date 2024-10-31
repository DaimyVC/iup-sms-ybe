#include "clause.h"
#include "useful.h"
#include <math.h>

void encodeEntries(cnf_t *cnf, vector<int> d, int &nextFree, matrixLits_t &cycset_lits)
{   for (int i = 0; i < problem_size; i++)
        for (int j = 0; j < problem_size; j++)
            for (int k = 0; k < problem_size; k++){
                if(smallerEncoding && i!=j && k!=d[i])
                    cycset_lits[i][j][k] = nextFree++;
                else if(!smallerEncoding)
                    cycset_lits[i][j][k] = nextFree++;
            }
    
    for(int i=0; i<problem_size; i++)
        for(int j=0; j<problem_size; j++)
            {if(i!=j)
                exactlyOne(cnf, cycset_lits[i][j], nextFree);}

    for(int i=0; i<problem_size; i++)
        for(int k=0; k<problem_size; k++)
        {
            if(d[i]==k)
                continue;

            vector<int> to_encode;
            for(int j=0; j<problem_size; j++)
                {if(j!=i)
                    to_encode.push_back(cycset_lits[i][j][k]);
                }
            exactlyOne(cnf,to_encode,nextFree);
        }
    
    if(!smallerEncoding){
        for(int i=0; i<problem_size; i++){
            vector<int> to_encode;
            to_encode.push_back(cycset_lits[i][i][d[i]]);
            cnf->push_back(to_encode);
            to_encode.clear();
            for(int k=0; k<problem_size; k++){
                to_encode.push_back(cycset_lits[k][k][i]);
            }
            exactlyOne(cnf,to_encode,nextFree);
        }
    }
}

void encodeOrder(cnf_t *cnf, vector<int> d, int &nextFree, matrixLits_t &cycset_lits_ord, matrixLits_t &cycset_lits)
{   for (int i = 0; i < problem_size; i++)
        for (int j = 0; j < problem_size; j++)
        {
            int prev=-1;
            for (int k = 0; k < problem_size-1; k++)
            {
                if(i!=j && k!=d[i])
                {
                    cycset_lits_ord[i][j][k] = nextFree++;
                    if(prev!=-1){
                        clause_t cl;
                        cl.push_back(-cycset_lits_ord[i][j][prev]);
                        cl.push_back(cycset_lits_ord[i][j][k]);
                        cnf->push_back(cl);
                        prev=k;
                    }
                    clause_t cll;
                    for(int l=0; l<=k; l++){
                        if(l!=d[i]){
                            clause_t cl = vector<int>{-cycset_lits[i][j][l],cycset_lits_ord[i][j][k]};
                            cll.push_back(cycset_lits[i][j][l]);
                            cnf->push_back(cl);
                        }
                    }
                    cll.push_back(-cycset_lits_ord[i][j][k]);
                    
                    cnf->push_back(cll);
                    if(prev==-1){
                        prev=k;
                    }
                }
            }
        }
}

void encodeEntries(cnf_t *cnf, int &nextFree, matrixLits_t &cycset_lits)
{
    for(int i=0; i<problem_size; i++)
        for(int j=0; j<problem_size; j++)
            exactlyOne(cnf, cycset_lits[i][j], nextFree);

    for(int i=0; i<problem_size; i++)
        for(int k=0; k<problem_size; k++)
        {
            vector<int> to_encode;
            //clause_t cl;
            for(int j=0; j<problem_size; j++)
                {
                    to_encode.push_back(cycset_lits[i][j][k]);
                }
            exactlyOne(cnf,to_encode,nextFree);
        }

    for(int i=0; i<problem_size; i++){
        vector<int> to_encode;
        for(int k=0; k<problem_size; k++){
            to_encode.push_back(cycset_lits[k][k][i]);
        }
        exactlyOne(cnf,to_encode,nextFree);
    }
}

void exactlyOne(cnf_t *cnf, vector<int> eo, int &nextFree)
{
    vector<int>toEO=vector<int>();
    for(int i : eo){
        if(i!=0)
            toEO.push_back(i);
    }
    if(noCommander){
        atMostOne(cnf, toEO);
        atLeastOne(cnf, toEO);
    }
    else
    {
        auto p=commanderEncoding(toEO, nextFree);
        for(auto cl : p.second)
            cnf->push_back(cl);
        atLeastOne(cnf, toEO);
    }
}

void atMostOne(cnf_t *cnf, vector<int> alo)
{
    clause_t cl;
    for(std::size_t i=0, max=alo.size(); i<max; i++)
        for(std::size_t j=i+1; j<max; j++)
        {
            cl.push_back(-alo[i]);
            cl.push_back(-alo[j]);
            cnf->push_back(cl);
            cl.clear();
        }
}

void atLeastOne(cnf_t *cnf, vector<int> amo)
{
    clause_t cl;
    for(std::size_t i = 0, max=amo.size(); i<max; i++)
        cl.push_back(amo[i]);
    cnf->push_back(cl);
}

pair<int,cnf_t> commanderEncoding(vector<int> amo, int &nextFree)
{
    int a,b,c;
    cnf_t clauses;
    if(amo.size()==0)
        return make_pair(0, cnf_t());
    if(amo.size()==1)
        return make_pair(amo[0], cnf_t());
    if(amo.size()==2)
    {
        a = amo[0];
        b = amo[1];
        c = 0;
        clauses = cnf_t();
    }
    if(amo.size()==3)
    {
        a = amo[0];
        b = amo[1];
        c = amo[2];
        clauses = cnf_t();
    }
    if(amo.size()>3)
    {
        int p=ceil(amo.size()/3);

        auto p1 = commanderEncoding(vector<int>(amo.begin(), amo.begin()+p), nextFree);
        auto p2 = commanderEncoding(vector<int>(amo.begin()+p, amo.begin()+2*p),nextFree);
        auto p3 = commanderEncoding(vector<int>(amo.begin()+2*p, amo.end()), nextFree);
        a = p1.first;
        b = p2.first;
        c = p3.first;

        for(auto cl : p1.second)
            clauses.push_back(cl);
        for(auto cl : p2.second)
            clauses.push_back(cl);
        for(auto cl : p3.second)
            clauses.push_back(cl);
    }

    int cmd = nextFree++;
    clause_t cl;
    cl.push_back(-a);
    cl.push_back(cmd);
    clauses.push_back(cl);
    cl.clear();

    cl.push_back(-b);
    cl.push_back(cmd);
    clauses.push_back(cl);
    cl.clear();

    cl.push_back(a);
    cl.push_back(b);
    if(c!=0)
    {
        cl.push_back(c);
        cl.push_back(-cmd);
        clauses.push_back(cl);
        cl.clear();

        cl.push_back(-c);
        cl.push_back(cmd);
        clauses.push_back(cl);
        cl.clear();
    }
    else
    {
        cl.push_back(-cmd);
        clauses.push_back(cl);
        cl.clear();
    }

    cl.push_back(-a);
    cl.push_back(-b);
    clauses.push_back(cl);
    cl.clear();

    if(c!=0)
    {
        cl.push_back(-a);
        cl.push_back(-c);
        clauses.push_back(cl);
        cl.clear();

        cl.push_back(-b);
        cl.push_back(-c);
        clauses.push_back(cl);
        cl.clear();
    }

    return make_pair(cmd,clauses);
}

void YBEClausesNew(cnf_t *cnf, int &nextFree, matrixLits_t &cycset_lits)
{
    vector<matrixLits_t> ybe_lits = vector<matrixLits_t>(problem_size, matrixLits_t(problem_size, vector<vector<lit_t>>(problem_size,vector<lit_t>(problem_size,0))));
    for (int i=0; i<problem_size; i++){
        for (int j=i+1; j<problem_size; j++){
            for(int k=0; k<problem_size; k++){
                for(int b=0; b<problem_size; b++){
                    ybe_lits[i][j][k][b]=nextFree++;
                }
                exactlyOne(cnf,ybe_lits[i][j][k],nextFree);
            }
        }
    }
    
    for (int i=0; i<problem_size; i++){
        for (int j=i+1; j<problem_size; j++){
            for(int k=0; k<problem_size; k++){
                for(int x=0; x<problem_size; x++){
                    for(int y=0; y<problem_size; y++){
                        for(int b=0; b<problem_size; b++){
                            clause_t cl;
                            cl.push_back(-cycset_lits[i][j][x]); //x!=d[i]
                            cl.push_back(-cycset_lits[i][k][y]); //i==k->y=d[i], else y!=d[i]
                            cl.push_back(-cycset_lits[x][y][b]); //x==y->b=d[i], else b!=d[i]
                            cl.push_back(ybe_lits[i][j][k][b]);
                            cnf->push_back(cl);

                            cl.clear();
                            cl.push_back(-cycset_lits[j][i][x]);
                            cl.push_back(-cycset_lits[j][k][y]);
                            cl.push_back(-cycset_lits[x][y][b]);
                            cl.push_back(ybe_lits[i][j][k][b]);
                            cnf->push_back(cl);
                        }
                    }
                }
            }
        }
    }
}

void YBEClausesNew(cnf_t *cnf, int &nextFree, matrixLits_t &cycset_lits, vector<int> diag)
{
    ybeLits_t ybe_lits = ybeLits_t(problem_size, matrixLits_t(problem_size, vector<vector<lit_t>>(problem_size,vector<lit_t>(problem_size,0))));
    
    for (int i=0; i<problem_size; i++){
        for (int j=i+1; j<problem_size; j++){
            for(int k=0; k<problem_size; k++){
                for(int x=0; x<problem_size; x++){
                    for(int y=0; y<problem_size; y++){
                        for(int b=0; b<problem_size; b++){
                            if(!smallerEncoding 
                            || (x!=diag[i] && ((i!=k&&diag[i]!=y) || (i==k&&diag[i]==y)) && ((x!=y&&diag[x]!=b) || (x==y&&diag[x]==b)))){
                                clause_t cl;
                                cl.push_back(-cycset_lits[i][j][x]);
                                if(!smallerEncoding || i!=k)
                                    cl.push_back(-cycset_lits[i][k][y]);
                                if(!smallerEncoding || x!=y)
                                    cl.push_back(-cycset_lits[x][y][b]);
                                if(ybe_lits[i][j][k][b]==0)
                                    ybe_lits[i][j][k][b]=nextFree++;
                                cl.push_back(ybe_lits[i][j][k][b]);
                                cnf->push_back(cl);
                            }
                            
                            if(!smallerEncoding 
                            || (x!=diag[j] && ((j!=k&&diag[j]!=y) || (j==k&&diag[j]==y)) && ((x!=y&&diag[x]!=b) || (x==y&&diag[x]==b)))){
                                clause_t cl;
                                cl.clear();
                                cl.push_back(-cycset_lits[j][i][x]);
                                if(!smallerEncoding || j!=k)
                                    cl.push_back(-cycset_lits[j][k][y]);
                                if(!smallerEncoding || x!=y)
                                    cl.push_back(-cycset_lits[x][y][b]);
                                if(ybe_lits[i][j][k][b]==0)
                                    ybe_lits[i][j][k][b]=nextFree++;
                                cl.push_back(ybe_lits[i][j][k][b]);
                                cnf->push_back(cl);
                            }
                        }
                    }
                }
            }
        }
    }

    for (int i=0; i<problem_size; i++){
        for (int j=i+1; j<problem_size; j++){
            for(int k=0; k<problem_size; k++){
                vector<int> litsCopy;
                copy(ybe_lits[i][j][k].begin(), ybe_lits[i][j][k].end(),back_inserter(litsCopy));
                litsCopy.erase(remove(litsCopy.begin(),litsCopy.end(),0),litsCopy.end());
                litsCopy.shrink_to_fit();
                exactlyOne(cnf,litsCopy,nextFree);
            }
        }
    }
}

void fixFirstRows(cnf_t *cnf, matrixLits_t &cycset_lits, vector<int> firstRow, int n){
    for(int j = 0; j<n; j++){
        for(int i=0;i<problem_size;i++){
            if(diagPart && i==j)
                continue;
            clause_t cl;
            cl.push_back(cycset_lits[j][i][firstRow[i]]);
            cnf->push_back(cl);
        }
    }
}

void unfixFirstRows(cnf_t *cnf, matrixLits_t &cycset_lits, vector<int> firstRow, int n){
    clause_t cl;
    for(int j=0;j<n;j++){
        for(int i=0;i<problem_size;i++){
            if(diagPart && i==j)
                continue;
            cl.push_back(-cycset_lits[j][i][firstRow[i]]);
        }
    }
    cnf->push_back(cl);
}