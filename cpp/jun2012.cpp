#include <iostream>
#include <memory>
#include <vector>
#include <set>
#include <map>
#include <stdexcept>

struct Formula {
	std::string u, v;
	enum type {EQ, NEQ};
	enum type x;
	
	friend std::ostream& operator<<(std::ostream& os, const Formula& f) {
		os << '(' << f.u << ((f.x == Formula::type::EQ)? " == " : " != ") << f.v << ')';
		return os;
	}
	
	friend bool operator<(const Formula& u, const Formula& v) {
		return true;
	}
	
	friend void nelson_open(std::map<std::string, std::pair<std::string, int>>& c, std::set<Formula>& E) {
		c.clear();
		// izdvajamo sve razlicite promenljive
		std::set<std::string> vars;
		for(const auto& e : E) {
			vars.insert(e.u);
			vars.insert(e.v);
		}
		
		// svakoj promenljivoj dodelimo oznaku
		int i = 0;
		for(const auto& v : vars) {
			c[v] = std::pair<std::string, int>({v, i++});
		}
		
		// za svaku jednakost menjamo oznake
		for(const auto & e : E) {
			auto& x = c[e.u];
			auto& y = c[e.v];
			if(x.second < y.second) {
				x.first = y.first;
			} else {
				y.first = x.first;
			}
		}
	}
	
	friend bool is_consequence(std::map<std::string, std::pair<std::string, int>>& c, const Formula &f) {
		try {
			// jako glupo resenje
			// samo iteriramo svaki kroz celu mapu
			// ako zabodu istu vrednost, to je to
			auto x = c[f.u].first;
			auto y = c[f.v].first;
			for(int i = 0; i < c.size(); i++) {
				x = c[x].first;
				y = c[y].first;
			}
			return x == y;
		} catch(std::out_of_range& e) {
			return false;
		}
	
	}
	
	friend bool is_SAT(std::vector<std::vector<Formula>>& DNF) {
		// za svaku klauzu u DNF, izdvajamo EQ i NEQ
		// imamo A && !C, gde je !C deo koji odgovara NEQ kada se izvuce
		// negacija ispred
		// ispred svih klauza izvucemo negaciju i dobijamo KNF
		// i on ima klauze oblika A => C, a negacija stoji ispred celog KNF-a
		// sada za svaku klauzu, vadimo prvo A i C
		// onda proveravamo za svaku formulu iz C da li je A => c
		// ako nije nijedna, DNF je zadovoljiv
		// ako smo obisli sve klauze i nismo stali, onda je nezadovoljiv
		for(auto& clause : DNF) {
			std::set<Formula> A, C;
			for(auto& f : clause) {
				if(f.x == Formula::type::EQ) {
					A.insert(f);
				} else {
					C.insert(f);
				}
			}
			std::map<std::string, std::pair<std::string, int>> mapa;
			nelson_open(mapa, A);
			
			bool flag = false;
			
			std::cout << "A\n";
			for(const auto& a : A)
				std::cout << a << '\n';
			
			std::cout << "C\n";
			for(const auto& c : C)
				std::cout << c << '\n';
				
			for(const auto& x : mapa) {
				std::cout << x.first << "-->" << x.second.first << '\n';
			}
			
			for(auto& c : C) {
				if(is_consequence(mapa, c)) {
					flag = true;
					break;
				}
			}
			
			if(!flag) return true;
		}
		
		return false;
	
	}
	
};

int main() {

	Formula f = Formula{"u", "v", Formula::type::EQ};
	
	std::cout << f << '\n';
	
	std::vector<Formula> s1, s2;

	std::set<Formula> s = {f, Formula{"v", "t", Formula::type::EQ}, Formula{"u", "t", Formula::type::EQ}};
	
	std::map<std::string, std::pair<std::string, int>> m;
	
	nelson_open(m, s);
	
	for(const auto& x : m) {
		std::cout << x.first << "-->" << x.second.first << '\n';
	}
	
	Formula f1 = Formula{"u", "z", Formula::type::NEQ};
	
	std::cout << is_consequence(m, f) << '\n' << is_consequence(m, f1) << '\n';
	
	std::vector<std::vector<Formula>> dnf = {{Formula{"u", "v", Formula::type::EQ}, Formula{"u", "t", Formula::type::EQ}, Formula{"v", "t", Formula::type::NEQ}}, {Formula{"s", "x", Formula::type::EQ}, Formula{"s", "y", Formula::type::NEQ}, Formula{"x", "y", Formula::type::EQ}}};
	
	std::cout << is_SAT(dnf) << '\n';

	return 0;
}
















