#include "transCheck.hpp"

vector<int> TransitivityCheck::constructOrbit(int el){
    vector<bool> inOrbit(cycset.matrix.size(),false);
    vector<int> orbitEl;
    vector<int> toProcess;

    inOrbit[el]=true;
    orbitEl.push_back(el);
    toProcess.push_back(el);

    while(toProcess.size()!=0){
        auto x = toProcess.back();
        toProcess.pop_back();
        for(int np =0; np<cycset.matrix.size(); np++){
            int y = cycset.matrix[np][x];
            if(y != -1 && !inOrbit[y]){
                inOrbit[y]=true;
                orbitEl.push_back(y);
                toProcess.push_back(y);
            }
            else if(y==-1){
                auto opts = cycset.bitdomains[np][x].options();
                for(auto op : opts){
                    if(!inOrbit[op]){
                        inOrbit[op]=true;
                        orbitEl.push_back(op);
                        toProcess.push_back(op);
                    }
                }
            }
        }
    }
    return orbitEl;
}
vector<vector<int>> TransitivityCheck::constructOrbits(){
    vector<bool> checked(cycset.matrix.size(),false);
    vector<vector<int>> orbits;

    for(int i=0; i<cycset.matrix.size(); i++){
        if(!checked[i]){
            auto orbit = constructOrbit(i);
            orbits.push_back(orbit);
            for(auto el : orbit)
                checked[el]=true;
        }
    }
    return orbits;
}
bool TransitivityCheck::TransCheck(cycle_set_t cycset){
    this->cycset=cycset;
    //for partial cycle sets "optimistic" orbits are constructed,
    //i.e., if a permutation CAN still map x to y, y is added to the orbit of x
    return constructOrbit(0).size()==cycset.matrix.size();
}

void TransitivityCheck::preventDecomposable(cycle_set_t cycset){
    if(TransCheck(cycset))
        return;

    auto orbits = constructOrbits();
    auto smallestOrbit = *min_element(orbits.begin(), orbits.end(),
        [](const vector<int>& a, const vector<int>& b) {
            return a.size() < b.size();
        });

    auto outsideOrbit=vector<int>();
    for(int i=0; i<cycset.matrix.size();i++)
        if(find(smallestOrbit.begin(),smallestOrbit.end(),i)==smallestOrbit.end())
            outsideOrbit.push_back(i);

    if(smallestOrbit.size()==1){
        cout << "CONSTRAINT NOT WORKING......." << endl;
    } else {
        clause_t cls = clause_t();
        for(auto inorbit : smallestOrbit){
            for(int i=0; i<cycset.matrix.size(); i++){
                for(int notinorbit : outsideOrbit){ 
                    if(i!=inorbit && cycset.matrix[i][i]!=notinorbit){
                        cls.push_back(cycset.cycset_lits[i][inorbit][notinorbit]);
                    }
                    // if(i!=notinorbit && cycset.matrix[i][i]!=inorbit){
                    //     cls.push_back(cycset.cycset_lits[i][notinorbit][inorbit]);
                    // }
                }
            }
        }
        throw cls;
    }
    
}