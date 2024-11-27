#include "minCheck_V2.h"
#include "global.h"
#include<queue>
#include<iterator>

MinCheck_V2::MinCheck_V2(){
    return;
}

MinCheck_V2::MinCheck_V2(vector<int> diag, vector<vector<vector<lit_t>>> cycset_lits){
    this->cycset_lits=cycset_lits;
    diagIsId=true;
    if(diagPart){
        this->diag=cyclePerm_t(diag);
        for(int i=0; i<problem_size; i++){
            if(this->diag.permOf(i)!=i){
                diagIsId=false;
            }
        }
    }
    if(useBit && diagPart)
        initialPart = make_shared<pperm_bit>(pperm_bit(diag));
    else if(diagPart)
        initialPart = make_shared<pperm_plain>(pperm_plain(diag));
    else{ //kan ook voor id diag (is sneller), maar beter: initial part = rijen die id zijn?
        vector<int> initPerm = vector<int>(problem_size,-1);
        iota(initPerm.begin(),initPerm.end(),0); 
        initialPart = make_shared<pperm_plain>(pperm_plain(initPerm));
    }
    if(incrMincheck){
        incrMinChecker=IncrMinCheck(this->diag,initialPart,diagIsId);
    }
}


void MinCheck_V2::MinCheck(cycle_set_t cycset){
    if(logging>0){
        printf("MINCHECK!!!!!!!\n");
        printPartiallyDefinedCycleSet(cycset);
        printDomains(cycset);
    }
    this->cycset=cycset;
    //setCycleSet(cycset);
    if(incrMincheck){
        if(complete){
            if(incrMinChecker.solveComplete(cycset)){
                vector<int> witness = incrMinChecker.extractCompletePerm();
                permFullyDefinedCheck(witness,0,1);
            }
        } else {
            if(incrMinChecker.solvePartial(cycset)){
                vector<int> witness = incrMinChecker.extractPartialPerm();
                permFullyDefinedCheck(witness,0,1); 
            }
        }
        
    } else {
        this->its=0;
        checkMinimality(initialPart, 0,0);
    }
}

//Backtracking algorithm
void MinCheck_V2::checkMinimality(shared_ptr<pperm_common> perm, int r, int d){
    if(logging>2){
        printf("row %d, depth %d\n",r,d);
        perm->print();
    }
    its++;
    if(!final && (its>=maxMC)){
        throw LimitReachedException();
    }
    vector<shared_ptr<pperm_common>> propagated_options = vector<shared_ptr<pperm_common>>();
    auto options = perm->options(r);
    filterOptions(perm, options, r, propagated_options);

    //depth first
    for(auto option : propagated_options){
        if(option->fullDefined()){
            vector<int> p = option->getPerm();
            permFullyDefinedCheck(p,0,r);
            continue;
        }
        
        if(r<problem_size-1){
            if(!final){
                if(options.size()>0 && d+1<=maxDepth)
                    checkMinimality(option,r+1,d+1);
                else if(options.size()==0)
                    checkMinimality(option,r+1,d);
            } else {
                if(options.size()>0)
                    checkMinimality(option,r+1,d+1);
                else
                    checkMinimality(option,r+1,d);
            }
        }
    }
}

bool MinCheck_V2::propagateDecision(shared_ptr<pperm_common> perm, int r){
    int dec = perm->permOf(r);
    auto cycle_og = diag.cycle(r);

    //ensure cycles match == ensure diag is fixed

    if(dec==r){
        for(int i=1; i<cycle_og.size(); i++){
            bool fixed = perm->fix(cycle_og[i],cycle_og[i]);
            if(!fixed)
                return false;
        }
        return true;
    } else if(find(cycle_og.begin(),cycle_og.end(),dec)!=cycle_og.end()){
        
        int dist = find(cycle_og.begin(),cycle_og.end(),dec)-cycle_og.begin();

        int size = cycle_og.size();
        for(int i=1; i<size; i++){
            bool fixed = perm->fix(cycle_og[i],cycle_og[(i+dist)%size]);
            if(!fixed)
                return false;
        }
        return true;
    } else { 
        auto cycle_perm = diag.cycle(dec);
        int size = cycle_og.size();
        if(cycle_perm.size()!=size)
            return false;
        for(int i=1; i<size;i++){
            bool fixed=perm->fix(cycle_og[i],cycle_perm[i]);
            if(!fixed)
                return false;
        }
        return true;
    }
}

bool MinCheck_V2::fixAndPropagate(shared_ptr<pperm_common> perm, int i, int j){
        bool fixed = perm->fix(i,j);

        if(fixed && !diagIsId)
            fixed=fixed&&propagateDecision(perm,i);
        
        return fixed;
}

void MinCheck_V2::extendPerm(shared_ptr<pperm_common> perm){
    if(!useBit || perm->fullDefined())
        return;

    for(int i=0; i<problem_size; i++){
        if(perm->permOf(i)==-1)
            fixAndPropagate(perm,i,perm->options(i).front());
    }
}

void MinCheck_V2::filterOptions(shared_ptr<pperm_common> perm, vector<int> &options, int r, vector<shared_ptr<pperm_common>> &options_prop){
    for(int i=0; i<options.size();i++){
        shared_ptr<pperm_common> copyPerm(nullptr);
        if(!perm->fixed(r)){
            copyPerm = perm->copyPerm();
            bool fixed = fixAndPropagate(copyPerm,r,options[i]);
            if(!fixed)
                continue;
        }
        else
            copyPerm = perm;
        
        int minog = cycset.bitdomains[0][r].firstel;
        bool minOgFixed=cycset.bitdomains[0][r].numTrue==1;

        auto permVal = cycset.bitdomains[copyPerm->permOf(0)][copyPerm->permOf(r)];
        int pv=-1;
        int inv=-1;
        if(permVal.numTrue==1){
            pv=permVal.firstel;
            inv=copyPerm->invPermOf(pv);
        }

        if(permVal.numTrue==1){
            if(inv!=-1){
                if(inv<minog){
                    extendPerm(copyPerm);
                    vector<int> p = copyPerm->getPerm();
                    addClauses(p,0,r,oldBreakingClauses,false);
                } else if (minOgFixed && inv==minog){
                    options_prop.push_back(copyPerm);
                } else if (propagateMincheck && inv==minog){
                    extendPerm(copyPerm);
                    vector<int> p = copyPerm->getPerm();
                    addClauses(p,0,r,oldBreakingClauses,true);
                } 
            } else {
                vector<int> opt = copyPerm->invOptions(pv);
                int inv = *min_element(opt.begin(),opt.end());
                if(inv<minog){
                    fixAndPropagate(copyPerm,inv,pv);
                    extendPerm(copyPerm);
                    vector<int> p = copyPerm->getPerm();
                    addClauses(p,0,r,oldBreakingClauses,false);
                } else if (minOgFixed && inv==minog){
                    fixAndPropagate(copyPerm,inv,pv);
                    options_prop.push_back(copyPerm);
                } else if(propagateMincheck && inv==minog){
                    fixAndPropagate(copyPerm,inv,pv);
                    extendPerm(copyPerm);
                    vector<int> p = copyPerm->getPerm();
                    addClauses(p,0,r,oldBreakingClauses,true);
                }
            }

        } else {
            int maxel = -1;
            int maxi = -1;

            vector<int> alreadyDefined = vector<int>();
            bool larger = false;
            for(auto pv : permVal.options()){
                auto iopt = copyPerm->invOptions(pv);
                if(copyPerm->permOf(0)==0 && copyPerm->permOf(r)==r){
                    if(iopt.size()==1){
                        if(iopt[0]<pv && (propagateMincheck||minOgFixed)){
                            extendPerm(copyPerm);
                            vector<int> p = copyPerm->getPerm();
                            addClauses(p,0,r,oldBreakingClauses,true);
                        } else if(iopt[0]>pv){
                            larger=true;
                        }
                    } else {
                        int newmin = *min_element(iopt.begin(),iopt.end());
                        int newmax = *max_element(iopt.begin(),iopt.end());
                        if(newmin<pv && (propagateMincheck||minOgFixed)){
                            fixAndPropagate(copyPerm,newmin,pv);
                            extendPerm(copyPerm);
                            vector<int> p = copyPerm->getPerm();
                            addClauses(p,0,r,oldBreakingClauses,true);
                        } else if(newmax>pv){
                            larger=true;
                        }
                    }
                } else {
                    if(iopt.size()==1){
                        alreadyDefined.push_back(iopt[0]);
                        maxel=max(maxel,iopt[0]);
                        continue;
                    } else {
                        int newmax = *max_element(iopt.begin(),iopt.end());
                        if(newmax>maxel){
                            maxel=newmax;
                            maxi=pv;
                        }
                    }
                }
            }

            if(copyPerm->permOf(0)==0 && copyPerm->permOf(r)==r){
                if(!larger){
                    options_prop.push_back(copyPerm);
                    continue;
                } else
                    break;
            }

            if(alreadyDefined.size()==permVal.numTrue){
                if(maxel<minog){
                    extendPerm(copyPerm);
                    vector<int> p = copyPerm->getPerm();
                    addClauses(p,0,r,oldBreakingClauses,false);
                } else if (!propagateMincheck && minog==maxel) {
                    options_prop.push_back(copyPerm);
                }else if(propagateMincheck && minog==maxel){
                    extendPerm(copyPerm);
                    vector<int> p = copyPerm->getPerm();
                    addClauses(p,0,r,oldBreakingClauses,true);
                }
                break;
            } else {
                if(maxel<minog){
                    fixAndPropagate(copyPerm,maxel,maxi);
                    extendPerm(copyPerm);
                    vector<int> p = copyPerm->getPerm();
                    addClauses(p,0,r,oldBreakingClauses,false);
                } else if(!propagateMincheck && minog==maxel){
                    fixAndPropagate(copyPerm,maxel,maxi);
                    options_prop.push_back(copyPerm);
                }else if(propagateMincheck && minog==maxel){
                    fixAndPropagate(copyPerm,maxel,maxi);
                    extendPerm(copyPerm);
                    vector<int> p = copyPerm->getPerm();
                    addClauses(p,0,r,oldBreakingClauses,true);
                } 
                break;
            }
        }
    }
}

/* void MinCheck_V2::filterOptions2(shared_ptr<pperm_common> perm, vector<int> &options, int r, vector<shared_ptr<pperm_common>> &options_prop){
    for(int i=0; i<options.size();i++){
        shared_ptr<pperm_common> copyPerm(nullptr);
        if(!perm->fixed(r)){
            copyPerm = perm->copyPerm();
            bool fixed = fixAndPropagate(copyPerm,r,options[i]);
            if(!fixed)
                continue;
        }
        else
            copyPerm = perm;
        
        int minog = cycset.bitdomains[0][r].firstel;
        bool minOgFixed=cycset.bitdomains[0][r].numTrue==1;

        auto permVal = cycset.bitdomains[copyPerm->permOf(0)][copyPerm->permOf(r)];
        int pv=-1;
        int inv=-1;
        if(permVal.numTrue==1){
            pv=permVal.firstel;
            inv=copyPerm->invPermOf(pv);
        }

        if(permVal.numTrue==1){
            if(inv!=-1){
                if(inv<minog){
                    extendPerm(copyPerm);
                    vector<int> p = copyPerm->getPerm();
                    addClauses(p,0,r,oldBreakingClauses,false);
                } else if (minOgFixed && inv==minog){
                    options_prop.push_back(copyPerm);
                } else if (propagateMincheck && inv==minog){
                    extendPerm(copyPerm);
                    vector<int> p = copyPerm->getPerm();
                    addClauses(p,0,r,oldBreakingClauses,true);
                } 
            } else {
                vector<int> opt = copyPerm->invOptions(pv);
                int inv = *min_element(opt.begin(),opt.end());
                if(inv<minog){
                    fixAndPropagate(copyPerm,inv,pv);
                    extendPerm(copyPerm);
                    vector<int> p = copyPerm->getPerm();
                    addClauses(p,0,r,oldBreakingClauses,false);
                } else if (minOgFixed && inv==minog){
                    fixAndPropagate(copyPerm,inv,pv);
                    options_prop.push_back(copyPerm);
                } else if(propagateMincheck && inv==minog){
                    fixAndPropagate(copyPerm,inv,pv);
                    extendPerm(copyPerm);
                    vector<int> p = copyPerm->getPerm();
                    addClauses(p,0,r,oldBreakingClauses,true);
                }
            }

        } else {
            int maxel = -1;
            int maxi = -1;

            vector<int> alreadyDefined = vector<int>();
            bool larger = false;
            for(auto pv : permVal.options()){
                auto iopt = copyPerm->invOptions(pv);
                if(copyPerm->permOf(0)==0 && copyPerm->permOf(r)==r){
                    if(iopt.size()==1){
                        if(iopt[0]<pv){
                            extendPerm(copyPerm);
                            vector<int> p = copyPerm->getPerm();
                            addClauses(p,0,r,oldBreakingClauses,true);
                        } else
                            continue;
                    } else {
                        int newmin = *min_element(iopt.begin(),iopt.end());
                        if(newmin<pv){
                            fixAndPropagate(copyPerm,newmin,pv);
                            extendPerm(copyPerm);
                            vector<int> p = copyPerm->getPerm();
                            addClauses(p,0,r,oldBreakingClauses,true);
                        } else
                            continue;
                    }
                } else {
                    if(iopt.size()==1){
                        alreadyDefined.push_back(iopt[0]);
                        maxel=max(maxel,iopt[0]);
                        continue;
                    } else {
                        int newmax = *max_element(iopt.begin(),iopt.end());
                        if(newmax>maxel){
                            maxel=newmax;
                            maxi=pv;
                        }
                    }
                }
            }

            if(copyPerm->permOf(0)==0 && copyPerm->permOf(r)==r)
                break;

            if(alreadyDefined.size()==permVal.numTrue){
                if(maxel<minog){
                    extendPerm(copyPerm);
                    vector<int> p = copyPerm->getPerm();
                    addClauses(p,0,r,oldBreakingClauses,false);
                } else if (!propagateMincheck && minog==maxel) {
                    options_prop.push_back(copyPerm);
                }else if(propagateMincheck && minog==maxel){
                    extendPerm(copyPerm);
                    vector<int> p = copyPerm->getPerm();
                    addClauses(p,0,r,oldBreakingClauses,true);
                }
                break;
            } else {
                if(maxel<minog){
                    fixAndPropagate(copyPerm,maxel,maxi);
                    extendPerm(copyPerm);
                    vector<int> p = copyPerm->getPerm();
                    addClauses(p,0,r,oldBreakingClauses,false);
                } else if(!propagateMincheck && minog==maxel){
                    fixAndPropagate(copyPerm,maxel,maxi);
                    options_prop.push_back(copyPerm);
                }else if(propagateMincheck && minog==maxel){
                    fixAndPropagate(copyPerm,maxel,maxi);
                    extendPerm(copyPerm);
                    vector<int> p = copyPerm->getPerm();
                    addClauses(p,0,r,oldBreakingClauses,true);
                } 
                break;
            }
        }
    }
} */

shared_ptr<pperm_common> MinCheck_V2::inverseUnkown(shared_ptr<pperm_common> perm, int ogVal, int permVal){
    for(int j=0;j<=ogVal;j++){
        if(perm->fixed(j))
            continue;
        auto options = perm->options(j);
        if(find(options.begin(),options.end(),permVal)!=options.end()){
            shared_ptr<pperm_common> copyPerm = perm->copyPerm();

            bool fixed = fixAndPropagate(copyPerm, j, permVal);

            if(fixed)
                return copyPerm;
        }
    }
    return perm;
}