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

void findWitness(cnf_t *cnf, int &nextFree, matrixLits_t &cycset_lits, matrixLits_t &perm_cycset_lits, vector<vector<lit_t>> &perm_lits, cyclePerm_t &diag, shared_ptr<pperm_common> initialPart, bool isId){
    //Encode original matrix
    for (int i = 0; i < problem_size; i++)
        for (int j = 0; j < problem_size; j++)
            for (int k = 0; k < problem_size; k++){
                if((i==j) || (diag.diag[i]==k))
                    continue;
                cycset_lits[i][j][k] = nextFree++;
            }

    //Encode permuted matrix
    for (int i = 0; i < problem_size; i++)
        for (int j = 0; j < problem_size; j++)
            for (int k = 0; k < problem_size; k++){
                if((i==j) || (diag.diag[i]==k))
                    continue;
                perm_cycset_lits[i][j][k] = nextFree++;
            }
    
    //Each cell can only contain one element
    for(int i=0; i<problem_size; i++)
        for(int j=0; j<problem_size; j++){
            if(i!=j){
                exactlyOne(cnf, cycset_lits[i][j], nextFree);
                exactlyOne(cnf, perm_cycset_lits[i][j], nextFree);
            }
        }
    //Each row in matrix can only contain unique elements
    for(int i=0; i<problem_size; i++)
        for(int k=0; k<problem_size; k++)
        {
            if(diag.diag[i]==k)
                continue;
            vector<int> to_encode;
            vector<int> to_encode_p;
            for(int j=0; j<problem_size; j++){
                if(i==j)
                    continue;
                to_encode.push_back(cycset_lits[i][j][k]);
                to_encode_p.push_back(perm_cycset_lits[i][j][k]);
                
            }
            exactlyOne(cnf,to_encode,nextFree);
            exactlyOne(cnf,to_encode_p,nextFree);
        }

    //Encode possible permutations
    if(isId){
        for(int i=0; i<problem_size;i++)
            for(int j=0;j<problem_size;j++)
                perm_lits[i][j]=nextFree++;
    } else {
        for(int i=0; i<problem_size;i++)
            for(int j : initialPart->options(i))
                perm_lits[i][j]=nextFree++;
    }

    vector<int> to_encode = vector<int>{};
    for(int i=0; i<problem_size;i++){
        to_encode.push_back(-perm_lits[i][i]);
    }
    cnf->push_back(to_encode);

    //permutation should be well-defined
    for(int i=0; i<problem_size;i++){
        exactlyOne(cnf,perm_lits[i],nextFree);
        vector<int> to_encode;
        for(int j=0; j<problem_size; j++){
            to_encode.push_back(perm_lits[j][i]);
        }
        exactlyOne(cnf,to_encode,nextFree);
    }

    //exclude impossible permutations if diagonal is not the identity
    if(!isId){
        for(int og=0; og<problem_size; og++){
            auto cycle_og = diag.cycle(og);
            for(int img : initialPart->options(og)){
                if(og==img){
                    for(int i=1; i<cycle_og.size(); i++){
                        if(cycle_og[i]==og)
                            continue;
                        cnf->push_back(vector<int>({-perm_lits[og][img],perm_lits[cycle_og[i]][cycle_og[i]]}));
                    }
                } else if(find(cycle_og.begin(),cycle_og.end(),img)!=cycle_og.end()){
                    
                    int dist = find(cycle_og.begin(),cycle_og.end(),img)-cycle_og.begin();

                    int size = cycle_og.size();
                    for(int i=1; i<size; i++){
                        cnf->push_back(vector<int>({-perm_lits[og][img],perm_lits[cycle_og[i]][cycle_og[(i+dist)%size]]}));
                    }
                } else { 
                    auto cycle_perm = diag.cycle(img);
                    int size = cycle_og.size();
                    for(int i=1; i<size;i++){
                        cnf->push_back(vector<int>({-perm_lits[og][img],perm_lits[cycle_og[i]][cycle_perm[i]]}));
                    }
                }
            }
        }
    }
    
    //Encode relation between og cycle set and its permutation
    for(int ogcol=0; ogcol<problem_size; ogcol++){
        for(int pmcol:initialPart->options(ogcol)){
            for(int ogrow=0; ogrow<problem_size; ogrow++){
                if(ogcol==ogrow)
                    continue;
                for(int pmrow:initialPart->options(ogrow)){
                    if(pmrow==pmcol)
                        continue;
                    for(int val=0;val<problem_size;val++){
                        if(val==diag.diag[pmrow])
                            continue;
                        for(int pmval:initialPart->invOptions(val)){
                            if(pmval==diag.diag[ogrow])
                                continue;
                            cnf->push_back({
                                -perm_lits[ogcol][pmcol],
                                -perm_lits[ogrow][pmrow],
                                cycset_lits[pmrow][pmcol][val],
                                -perm_lits[pmval][val],
                                -perm_cycset_lits[ogrow][ogcol][pmval]
                                });
                            cnf->push_back({
                                -perm_lits[ogcol][pmcol],
                                -perm_lits[ogrow][pmrow],
                                -cycset_lits[pmrow][pmcol][val],
                                -perm_lits[pmval][val],
                                perm_cycset_lits[ogrow][ogcol][pmval]
                                });
                        }   
                    }
                }
            }
        }
    }

    //Force permutation to be smaller using SBC
    int auxprev=0;
    int aux = nextFree++;
    clause_t cl={aux};
    cnf->push_back(cl);
    for(int row=0;row<problem_size;row++){
        for(int col=0;col<problem_size;col++){
            if(row==col)
                continue;
            for(int val=problem_size-1;val>=0;val--){
                if(val==diag.diag[row])
                    continue;
                auxprev=aux;
                aux=nextFree++;
                cnf->push_back({-auxprev,cycset_lits[row][col][val],-perm_cycset_lits[row][col][val]});
                if((row!=problem_size-1) || (col!=problem_size-2) || (val!= (diag.diag[problem_size-1]==0?1:0))){
                    cnf->push_back({aux,-auxprev,cycset_lits[row][col][val]});
                    cnf->push_back({aux,-auxprev,-perm_cycset_lits[row][col][val]});
                } else {
                    cnf->push_back({-auxprev,cycset_lits[row][col][val]});
                    cnf->push_back({-auxprev,-perm_cycset_lits[row][col][val]});
                }
            }
        }
    }
}

void findPartialWitness(cnf_t *cnf, int &nextFree, matrixLits_t &cycset_lits, matrixLits_t &perm_cycset_lits, vector<vector<lit_t>> &perm_lits, matrixLits_t &larger, cyclePerm_t &diag, shared_ptr<pperm_common> initialPart, bool isId){
    
    matrixLits_t smaller=vector<vector<vector<int>>>(problem_size, vector<vector<int>>(problem_size, vector<int>(problem_size, 0)));
    vector<vector<int>> notBroken=vector<vector<int>>(problem_size, vector<int>(problem_size, 0));
    
    
    //Encode original matrix
    for (int i = 0; i < problem_size; i++)
        for (int j = 0; j < problem_size; j++)
            for (int k = 0; k < problem_size; k++){
                if((i==j) || (diag.diag[i]==k))
                    continue;
                cycset_lits[i][j][k] = nextFree++;
            }

    //Encode permuted matrix
    for (int i = 0; i < problem_size; i++)
        for (int j = 0; j < problem_size; j++)
            for (int k = 0; k < problem_size; k++){
                if((i==j) || (diag.diag[i]==k))
                    continue;
                perm_cycset_lits[i][j][k] = nextFree++;
            }

    //Encode possible permutations
    if(isId){
        for(int i=0; i<problem_size;i++)
            for(int j=0;j<problem_size;j++)
                perm_lits[i][j]=nextFree++;
    } else {
        for(int i=0; i<problem_size;i++)
            for(int j : initialPart->options(i))
                perm_lits[i][j]=nextFree++;
    }

    vector<int> to_encode = vector<int>{};
    for(int i=0; i<problem_size;i++){
        to_encode.push_back(-perm_lits[i][i]);
    }
    cnf->push_back(to_encode);

    //permutation should be well-defined
    for(int i=0; i<problem_size;i++){
        exactlyOne(cnf,perm_lits[i],nextFree);
        vector<int> to_encode;
        for(int j=0; j<problem_size; j++){
            to_encode.push_back(perm_lits[j][i]);
        }
        exactlyOne(cnf,to_encode,nextFree);
    }

    //exclude impossible permutations if diagonal is not the identity
    if(!isId){
        for(int og=0; og<problem_size; og++){
            auto cycle_og = diag.cycle(og);
            for(int img : initialPart->options(og)){
                if(og==img){
                    for(int i=1; i<cycle_og.size(); i++){
                        if(cycle_og[i]==og)
                            continue;
                        cnf->push_back(vector<int>({-perm_lits[og][img],perm_lits[cycle_og[i]][cycle_og[i]]}));
                    }
                } else if(find(cycle_og.begin(),cycle_og.end(),img)!=cycle_og.end()){
                    
                    int dist = find(cycle_og.begin(),cycle_og.end(),img)-cycle_og.begin();

                    int size = cycle_og.size();
                    for(int i=1; i<size; i++){
                        cnf->push_back(vector<int>({-perm_lits[og][img],perm_lits[cycle_og[i]][cycle_og[(i+dist)%size]]}));
                    }
                } else { 
                    auto cycle_perm = diag.cycle(img);
                    int size = cycle_og.size();
                    for(int i=1; i<size;i++){
                        cnf->push_back(vector<int>({-perm_lits[og][img],perm_lits[cycle_og[i]][cycle_perm[i]]}));
                    }
                }
            }
        }
    }
    
    //Encode relation between og cycle set and its permutation
    for(int ogcol=0; ogcol<problem_size; ogcol++){
        for(int pmcol:initialPart->options(ogcol)){
            for(int ogrow=0; ogrow<problem_size; ogrow++){
                if(ogcol==ogrow)
                    continue;
                for(int pmrow:initialPart->options(ogrow)){
                    if(pmrow==pmcol)
                        continue;
                    for(int val=0;val<problem_size;val++){
                        if(val==diag.diag[pmrow])
                            continue;
                        for(int pmval:initialPart->invOptions(val)){
                            if(pmval==diag.diag[ogrow])
                                continue;
                            cnf->push_back({
                                -perm_lits[ogcol][pmcol],
                                -perm_lits[ogrow][pmrow],
                                cycset_lits[pmrow][pmcol][val],
                                -perm_lits[pmval][val],
                                -perm_cycset_lits[ogrow][ogcol][pmval]
                                });
                            cnf->push_back({
                                -perm_lits[ogcol][pmcol],
                                -perm_lits[ogrow][pmrow],
                                -cycset_lits[pmrow][pmcol][val],
                                -perm_lits[pmval][val],
                                perm_cycset_lits[ogrow][ogcol][pmval]
                                });
                        }   
                    }
                }
            }
        }
    }

    for(int row=0;row<problem_size;row++){
        for(int col=0;col<problem_size;col ++){
            if(row==col)
                continue;
            for(int val=0; val<problem_size;val++){
                    larger[row][col][val]=nextFree++;
                    vector<int> toAdd=vector<int>();
                    for(int k=0;k<=val;k++){
                        if(k==diag.diag[row])
                            continue;
                        toAdd.push_back(cycset_lits[row][col][k]);
                        cnf->push_back({-larger[row][col][val],-cycset_lits[row][col][k]});
                    }
                    toAdd.push_back(larger[row][col][val]);
                    cnf->push_back(toAdd);
            }
        }
    }

    for(int row=0;row<problem_size;row++){
        for(int col=0;col<problem_size;col ++){
            if(row==col)
                continue;
            for(int val=0; val<problem_size;val++){
                    smaller[row][col][val]=nextFree++;
                    vector<int> toAdd=vector<int>();
                    for(int k=val;k<problem_size;k++){
                        if(k==diag.diag[row])
                            continue;
                        toAdd.push_back(perm_cycset_lits[row][col][k]);
                        cnf->push_back({-smaller[row][col][val],-perm_cycset_lits[row][col][k]});
                    }
                    toAdd.push_back(smaller[row][col][val]);
                    cnf->push_back(toAdd);
            }
        }
    }

    //Force permutation to be smaller using SBC
    int auxprev=0;
    int aux = nextFree++;
    int numAdded=0;
    clause_t cl={aux};
    cnf->push_back(cl);
    for(int row=0;row<problem_size;row++){
        for(int col=0;col<problem_size;col++){
            if(row==col)
                continue;
            for(int val=problem_size-1;val>=0;val--){
                if(val==diag.diag[row])
                    continue;
                auxprev=aux;
                aux=nextFree++;
                if(val==0){
                    numAdded+=1;
                    if(((row!=problem_size-1) || (col!=problem_size-2) || (val!=(diag.diag[problem_size-1]==0?1:0))) && (numAdded<maxMC)){
                        cnf->push_back({aux,-auxprev,smaller[row][col][val]});
                        cnf->push_back({aux,-auxprev,cycset_lits[row][col][val]});
                    } else {
                        cnf->push_back({-auxprev,smaller[row][col][val]});
                        cnf->push_back({aux,-auxprev,cycset_lits[row][col][val]});
                        goto end;
                    }
                }else{
                    cnf->push_back({-auxprev,larger[row][col][val-1],smaller[row][col][val]});
                    numAdded+=1;
                    if(((row!=problem_size-1) || (col!=problem_size-2) || (val!=(diag.diag[problem_size-1]==0?1:0))) && (numAdded<maxMC)){
                        cnf->push_back({aux,-auxprev,smaller[row][col][val]});
                        cnf->push_back({aux,-auxprev,cycset_lits[row][col][val]});
                    } else {
                        cnf->push_back({-auxprev,smaller[row][col][val]});
                        cnf->push_back({aux,-auxprev,cycset_lits[row][col][val]});
                        goto end;
                    }
                }
            }
        }
    }

    end:
        return;
}

void findPartialWitness2(cnf_t *cnf, int &nextFree, matrixLits_t &cycset_lits, matrixLits_t &perm_cycset_lits, vector<vector<lit_t>> &perm_lits, matrixLits_t &larger, cyclePerm_t &diag, shared_ptr<pperm_common> initialPart, bool isId){
    
    matrixLits_t smaller=vector<vector<vector<int>>>(problem_size, vector<vector<int>>(problem_size, vector<int>(problem_size, 0)));
    vector<vector<int>> notBroken=vector<vector<int>>(problem_size, vector<int>(problem_size, 0));
    
    
    //Encode original matrix
    for (int i = 0; i < problem_size; i++)
        for (int j = 0; j < problem_size; j++)
            for (int k = 0; k < problem_size; k++){
                if((i==j) || (diag.diag[i]==k))
                    continue;
                cycset_lits[i][j][k] = nextFree++;
            }

    //og>x vars
    for(int row=0; row<problem_size; row++){
        for(int col=0; col<problem_size; col++){
            if(row==col)
                continue;
            for(int val=0; val<problem_size; val++){
                larger[row][col][val]=nextFree++;
                vector<int> toAdd=vector<int>();
                for(int k=0;k<=val;k++){
                    if(k==diag.diag[row])
                        continue;
                    toAdd.push_back(cycset_lits[row][col][k]);
                    cnf->push_back({-larger[row][col][val],-cycset_lits[row][col][k]});
                }
                toAdd.push_back(larger[row][col][val]);
                cnf->push_back(toAdd);
            }
        }
    }

    //Encode permuted matrix
    for (int i = 0; i < problem_size; i++)
        for (int j = 0; j < problem_size; j++)
            for (int k = 0; k < problem_size; k++){
                if((i==j) || (diag.diag[i]==k))
                    continue;
                perm_cycset_lits[i][j][k] = nextFree++;
            }

    //perm<x vars
    for(int row=0;row<problem_size;row++){
        for(int col=0;col<problem_size;col ++){
            if(row==col)
                continue;
            for(int val=0; val<problem_size;val++){
                smaller[row][col][val]=nextFree++;
                vector<int> toAdd=vector<int>();
                for(int k=val;k<problem_size;k++){
                    if(k==diag.diag[row])
                        continue;
                    toAdd.push_back(perm_cycset_lits[row][col][k]);
                    cnf->push_back({-smaller[row][col][val],-perm_cycset_lits[row][col][k]});
                }
                toAdd.push_back(smaller[row][col][val]);
                cnf->push_back(toAdd);
            }
        }
    }

    //Encode possible permutations
    if(isId){
        for(int i=0; i<problem_size;i++)
            for(int j=0;j<problem_size;j++)
                perm_lits[i][j]=nextFree++;
    } else {
        for(int i=0; i<problem_size;i++)
            for(int j : initialPart->options(i))
                perm_lits[i][j]=nextFree++;
    }

    vector<int> to_encode = vector<int>{};
    for(int i=0; i<problem_size;i++){
        to_encode.push_back(-perm_lits[i][i]);
    }
    cnf->push_back(to_encode);

    //permutation should be well-defined
    for(int i=0; i<problem_size;i++){
        exactlyOne(cnf,perm_lits[i],nextFree);
        vector<int> to_encode;
        for(int j=0; j<problem_size; j++){
            to_encode.push_back(perm_lits[j][i]);
        }
        exactlyOne(cnf,to_encode,nextFree);
    }

    //exclude impossible permutations if diagonal is not the identity
    if(!isId){
        for(int og=0; og<problem_size; og++){
            auto cycle_og = diag.cycle(og);
            for(int img : initialPart->options(og)){
                if(og==img){
                    for(int i=1; i<cycle_og.size(); i++){
                        if(cycle_og[i]==og)
                            continue;
                        cnf->push_back(vector<int>({-perm_lits[og][img],perm_lits[cycle_og[i]][cycle_og[i]]}));
                    }
                } else if(find(cycle_og.begin(),cycle_og.end(),img)!=cycle_og.end()){
                    
                    int dist = find(cycle_og.begin(),cycle_og.end(),img)-cycle_og.begin();

                    int size = cycle_og.size();
                    for(int i=1; i<size; i++){
                        cnf->push_back(vector<int>({-perm_lits[og][img],perm_lits[cycle_og[i]][cycle_og[(i+dist)%size]]}));
                    }
                } else { 
                    auto cycle_perm = diag.cycle(img);
                    int size = cycle_og.size();
                    for(int i=1; i<size;i++){
                        cnf->push_back(vector<int>({-perm_lits[og][img],perm_lits[cycle_og[i]][cycle_perm[i]]}));
                    }
                }
            }
        }
    }
    
    //Encode relation between og cycle set and its permutation
    for(int ogcol=0; ogcol<problem_size; ogcol++){
        for(int pmcol:initialPart->options(ogcol)){
            for(int ogrow=0; ogrow<problem_size; ogrow++){
                if(ogcol==ogrow)
                    continue;
                for(int pmrow:initialPart->options(ogrow)){
                    if(pmrow==pmcol)
                        continue;
                    for(int val=0;val<problem_size;val++){
                        if(val==diag.diag[pmrow])
                            continue;
                        for(int pmval:initialPart->invOptions(val)){
                            if(pmval==diag.diag[ogrow])
                                continue;
                            cnf->push_back({
                                -perm_lits[ogcol][pmcol],
                                -perm_lits[ogrow][pmrow],
                                cycset_lits[pmrow][pmcol][val],
                                -perm_lits[pmval][val],
                                -perm_cycset_lits[ogrow][ogcol][pmval]
                                });
                            cnf->push_back({
                                -perm_lits[ogcol][pmcol],
                                -perm_lits[ogrow][pmrow],
                                -cycset_lits[pmrow][pmcol][val],
                                -perm_lits[pmval][val],
                                perm_cycset_lits[ogrow][ogcol][pmval]
                                });
                        }   
                    }
                }
            }
        }
    }

    //SBC
    int prevrow=0;
    int prevcol=0;
    notBroken[prevrow][prevcol]=nextFree++;
    cnf->push_back({notBroken[prevrow][prevcol]});
    for(int r=0;r<problem_size;r++){
        for(int c=0; c<problem_size; c++){
            if(r==c)
                continue;

            notBroken[r][c]=nextFree++;
            if((r==problem_size-1) && (c==problem_size-2)){
                for(int v=0; v<problem_size; v++){
                    if(v!=0&&v!=problem_size-1){
                        cnf->push_back({-notBroken[prevrow][prevcol],smaller[r][c][v+1],larger[r][c][v-1]});
                    }
                }
            } else {
                for(int v=0; v<problem_size; v++){
                    if(v!=0&&v!=problem_size-1){
                        cnf->push_back({-notBroken[prevrow][prevcol],smaller[r][c][v+1],larger[r][c][v-1]});
                    }
                    if(v!=diag.diag[r]){
                        cnf->push_back({-notBroken[prevrow][prevcol],-cycset_lits[r][c][v],-perm_cycset_lits[r][c][v],notBroken[r][c]});
                    }
                }
            }
            prevrow=r;
            prevcol=c;
        }
    }
}