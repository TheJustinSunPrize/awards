// Untrusted certificate discovery. All resulting equations are checked by Lean rfl.
#include <unordered_map>
#include <vector>
#include <iostream>
#include <fstream>
#include <cstdint>
int main(){std::unordered_map<uint64_t,uint32_t> nodes;std::vector<uint64_t> states;std::vector<uint32_t> roots;size_t longest=0;
for(uint32_t n=2;n<=10000;n++){uint32_t a=n,r=n;std::vector<uint64_t> path;while(r){uint64_t key=((uint64_t)a<<32)|r;if(nodes.count(key))break;path.push_back(key);a++;r*=2;if(r>=a)r-=a;if(a>10000000){std::cout<<"FAIL "<<n;return 1;}}if(path.size()>longest)longest=path.size();for(auto it=path.rbegin();it!=path.rend();++it){states.push_back(*it);nodes[*it]=states.size();}roots.push_back(nodes[((uint64_t)n<<32)|n]);if(n%1000==0)std::cout<<n<<" nodes "<<nodes.size()<<" longest "<<longest<<std::endl;}
std::ofstream o("generated-work/greedy-dag.tsv");for(auto key:states){uint32_t a=key>>32,r=key;uint32_t next=2*r>=a+1?2*r-a-1:2*r;auto it=nodes.find(((uint64_t)(a+1)<<32)|next);o<<a<<'\t'<<r<<'\t'<<(next?it->second:0)<<'\n';}
}
