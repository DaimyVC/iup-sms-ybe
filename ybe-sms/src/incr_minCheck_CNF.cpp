#include "useful.h"
#include "global.h"
#include "incr_minCheck.h"

void IncrMinCheck::findWitness(cnf_t *cnf, int &nextFree){
    
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

void IncrMinCheck::findPartialWitness(cnf_t *cnf, int &nextFree){

    vector<vector<int>> notBroken=vector<vector<int>>(problem_size, vector<int>(problem_size, 0));

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
                    vector<int> toAdd=vector<int>();
                    for(int k=0;k<val;k++){
                        if(k==diag.diag[row])
                            continue;
                        toAdd.push_back(cycset_lits[row][col][k]);
                        cnf->push_back({-largerEQ_lits[row][col][val],-cycset_lits[row][col][k]});
                    }
                    toAdd.push_back(largerEQ_lits[row][col][val]);
                    cnf->push_back(toAdd);
            }
        }
    }

    for(int row=0;row<problem_size;row++){
        for(int col=0;col<problem_size;col ++){
            if(row==col)
                continue;
            for(int val=0; val<problem_size;val++){
                    vector<int> toAdd=vector<int>();
                    for(int k=val+1;k<problem_size;k++){
                        if(k==diag.diag[row])
                            continue;
                        toAdd.push_back(perm_cycset_lits[row][col][k]);
                        cnf->push_back({-smallerEQ_lits[row][col][val],-perm_cycset_lits[row][col][k]});
                    }
                    toAdd.push_back(smallerEQ_lits[row][col][val]);
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
                        cnf->push_back({aux,-auxprev});
                        cnf->push_back({aux,-auxprev,cycset_lits[row][col][val]});
                    } else {
                        cnf->push_back({-auxprev});
                        cnf->push_back({-auxprev,cycset_lits[row][col][val]});
                        goto end;
                    }
                }else{
                    cnf->push_back({-auxprev,largerEQ_lits[row][col][val],smallerEQ_lits[row][col][val-1]});
                    numAdded+=1;
                    if(((row!=problem_size-1) || (col!=problem_size-2) || (val!=(diag.diag[problem_size-1]==0?1:0))) && (numAdded<maxMC)){
                        cnf->push_back({aux,-auxprev,smallerEQ_lits[row][col][val-1]});
                        cnf->push_back({aux,-auxprev,cycset_lits[row][col][val]});
                    } else {
                        cnf->push_back({-auxprev,smallerEQ_lits[row][col][val-1 ]});
                        cnf->push_back({-auxprev,cycset_lits[row][col][val]});
                        goto end;
                    }
                }
            }
        }
    }

    end:
        return;
}

void IncrMinCheck::findPartialWitnessV2(cnf_t *cnf, int &nextFree){
    vector<vector<int>> notBroken=vector<vector<int>>(problem_size, vector<int>(problem_size, 0));
    vector<vector<int>> fixed=vector<vector<int>>(problem_size, vector<int>(problem_size, 0));
    vector<vector<int>> matLess=vector<vector<int>>(problem_size, vector<int>(problem_size, 0));
    vector<vector<int>> matStrictlyLess=vector<vector<int>>(problem_size, vector<int>(problem_size, 0));

    //og>=x vars
    for(int row=0; row<problem_size; row++){
        for(int col=0; col<problem_size; col++){
            if(row==col)
                continue;
            for(int val=0; val<problem_size; val++){
                vector<int> toAdd=vector<int>();
                for(int k=0;k<val;k++){
                    if(k==diag.diag[row])
                        continue;
                    toAdd.push_back(cycset_lits[row][col][k]);
                    cnf->push_back({-largerEQ_lits[row][col][val],-cycset_lits[row][col][k]});
                }
                toAdd.push_back(largerEQ_lits[row][col][val]);
                cnf->push_back(toAdd);
            }
        }
    }

    //perm<=x vars
    for(int row=0;row<problem_size;row++){
        for(int col=0;col<problem_size;col ++){
            if(row==col)
                continue;
            for(int val=0; val<problem_size;val++){
                vector<int> toAdd=vector<int>();
                for(int k=val+1;k<problem_size;k++){
                    if(k==diag.diag[row])
                        continue;
                    toAdd.push_back(perm_cycset_lits[row][col][k]);
                    cnf->push_back({-smallerEQ_lits[row][col][val],-perm_cycset_lits[row][col][k]});
                }
                toAdd.push_back(smallerEQ_lits[row][col][val]);
                cnf->push_back(toAdd);
            }
        }
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
 
    //encode f_{i,j} variables where f_{i,j} is true if the permutation fixes all possible values of M_{i,j} as well as i and j
    for(int i=0;i<problem_size; i++){
        for(int j=0; j<problem_size; j++){
            if(i==j)
                continue;
            
            vector<lit_t> to_add=vector<lit_t>();
            for(int k=0; k<problem_size; k++){
                if(k==diag.diag[i])
                    continue;
                
                lit_t aux = nextFree++;
                cnf->push_back({-aux,-cycset_lits[i][j][k],perm_lits[k][k]});
                cnf->push_back({aux,cycset_lits[i][j][k]});
                cnf->push_back({aux,-perm_lits[k][k]});
                to_add.push_back(aux);
            }
            fixed[i][j]=nextFree++;
            vector<lit_t> cls=vector<lit_t>({fixed[i][j],-perm_lits[i][i],-perm_lits[j][j]});
            cnf->push_back({-fixed[i][j],perm_lits[i][i]});
            cnf->push_back({-fixed[i][j],perm_lits[j][j]});
            for(auto lit : to_add){
                cnf->push_back({-fixed[i][j],lit});
                cls.push_back(-lit);
            }
            cnf->push_back({-fixed[i][j],perm_lits[i][i]});
            cnf->push_back(cls);
        }
    }

    for(int i=0; i<problem_size; i++){
        for(int j=0; j<problem_size; j++){
            if(i==j)
                continue;
            
            matStrictlyLess[i][j]=nextFree++;
            vector<lit_t> toAdd = vector<lit_t>({-matStrictlyLess[i][j]});
            for(int k=0; k<problem_size-1; k++){
                lit_t aux=nextFree++;
                //aux <=> Mij>k AND s(M)ij<=k (i.e. Mij>=k+1 AND s(M)<=k)
                cnf->push_back({aux,-largerEQ_lits[i][j][k+1],-smallerEQ_lits[i][j][k]});
                cnf->push_back({-aux,largerEQ_lits[i][j][k+1]});
                cnf->push_back({-aux,smallerEQ_lits[i][j][k]});
                toAdd.push_back(aux);
                cnf->push_back({-aux,matStrictlyLess[i][j]});
            }
            cnf->push_back(toAdd);
        }
    }

    for(int i=0; i<problem_size; i++){
        for(int j=0; j<problem_size; j++){
            if(i==j)
                continue;
            
            matLess[i][j]=nextFree++;
            vector<lit_t> toAdd = vector<lit_t>({-matLess[i][j],fixed[i][j]});
            for(int k=0; k<problem_size; k++){
                lit_t aux=nextFree++;
                cnf->push_back({aux,-largerEQ_lits[i][j][k],-smallerEQ_lits[i][j][k]});
                cnf->push_back({-aux,largerEQ_lits[i][j][k]});
                cnf->push_back({-aux,smallerEQ_lits[i][j][k]});
                toAdd.push_back(aux);
                cnf->push_back({-aux,matLess[i][j]});
            }
            cnf->push_back({-fixed[i][j],matLess[i][j]});
            cnf->push_back(toAdd);
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
                cnf->push_back({-notBroken[prevrow][prevcol],matStrictlyLess[r][c]});
            } else {
                cnf->push_back({-notBroken[prevrow][prevcol],matLess[r][c]});
                cnf->push_back({-notBroken[prevrow][prevcol],-matLess[r][c],matStrictlyLess[r][c],notBroken[r][c]});
            }
            prevrow=r;
            prevcol=c;
        }
    }
}