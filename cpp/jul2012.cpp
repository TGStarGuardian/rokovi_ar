#include <iostream>
#include <memory>
#include <vector>
#include <typeinfo>
#include <tuple>

class Term;
class Atom;

using T = std::shared_ptr<Term>;
using A = std::shared_ptr<Atom>;

// term ima u sebi samo konstante
// i eventualno poziv funkcije
class Term {
	public:
		virtual void print(std::ostream& os) const = 0;
		friend std::ostream& operator<<(std::ostream& os, const T& term) {
			term->print(os);
			return os;
		}
		
		virtual bool operator==(const T& t) const = 0;
		
		friend bool operator==(const T& t1, const T& t2) {
			return *t1 == t2;
		}
};

class ConstantTerm : public Term {
	public:
		ConstantTerm(const std::string& name): name(name) {}
		
		void print(std::ostream& os) const {
			os << name;
		}
		
		const std::string& get_name() const {
			return name;
		}
		
		bool operator==(const T& t) const {
			// probamo da konvertujemo t u ConstantTerm
			auto x = std::dynamic_pointer_cast<ConstantTerm>(t);
			return x != nullptr && name == x->get_name();
		}
		
	private:
		std::string name;


};


class FunctionTerm : public Term {
	public:
		FunctionTerm(const std::string& s, const std::vector<T>& a): symbol(s), args(a) {}
		
		void print(std::ostream& os) const {
			os << symbol << '(';
			for(int i = 0; i < args.size(); i++) {
				os << args[i] << ((i == args.size() - 1)? ")" : ", ");
			}
		}
		
		const std::string& get_symbol() const {
			return symbol;
		}
		
		const std::vector<T>& get_args() const {
			return args;
		}
		
		friend bool operator==(std::vector<T>& args1, std::vector<T>& args2) {
			if(args1.size() != args2.size()) return false;
			
			auto it1 = args1.begin(), it2 = args2.begin();
			
			for( ; it1 != args1.end() && it2 != args2.end(); ++it1, ++it2) {
				if(*it1 != *it2) return false;
			}
			
			return true;
		}
		
		bool operator==(const T& t) const {
			auto x = std::dynamic_pointer_cast<FunctionTerm>(t);
			return x != nullptr && symbol == x->get_symbol() && args == x->get_args();
		}
	
	private:
		std::string symbol;
		std::vector<T> args;
};


class Atom {
	public:
		Atom(const std::string& s, const std::vector<T>& a):
			symbol(s), args(a) {}
		
		friend std::ostream& operator<<(std::ostream& os, const A& atom) {
			os << atom->symbol;
			if(!atom->args.empty()) {
				os << "(";
				for(int i = 0; i < atom->args.size(); i++) {
					os << atom->args[i] << ((i == atom->args.size() - 1)? ")" : ", ");
				}
			}
			
			return os;
		}
		
		friend bool operator==(const A& a1, const A& a2) {
			return a1->symbol == a2->symbol && a1->args == a2->args;
		
		}
	
	private:
		// da oznacimo ima li negaciju uz sebe
		std::string symbol;
		std::vector<T> args;
};

class HornClause {
	public:
		virtual void print(std::ostream&) = 0;
		friend std::ostream& operator<<(std::ostream& os, HornClause& h) {
			h.print(os);
			return os;
		}
};

class Resolvent1 {
	public:
		virtual A get_pos() const = 0;
		virtual std::vector<A> get_neg() const = 0;
}; 
class Resolvent2 {
	public:
		virtual std::vector<A> get_neg() const = 0;
};

class HornFact : public HornClause, public Resolvent1 {
	public:
		HornFact(const A& literal):
			pos(literal) {}
			
		void print(std::ostream& os) {
			os << '{' << pos << '}';
		}
		
		A get_pos() const {
			return pos;
		}
		
		std::vector<A> get_neg() const {
			return {};
		}
	
	private:
		A pos;
};

class HornRule: public HornClause, public Resolvent1 {
	public:
		HornRule(const A& pos, const std::vector<A>& neg):
			pos(pos), neg(neg) {}
			
		void print(std::ostream& os) {
			os << '{' << pos << ", ";
			for(int i = 0; i < neg.size(); i++) {
				os << '!' << neg[i] << ((i == neg.size() - 1)? ")" : ", ");
			}
			os << '}';
		}
		
		A get_pos() const {
			return pos;
		}
		
		std::vector<A> get_neg() const {
			return neg;
		}
	
	private:
		A pos;
		std::vector<A> neg;
};

class HornQuery : public HornClause, public Resolvent2 {
	public:
		HornQuery(const std::vector<A>& neg):
			neg(neg) {}
			
		void print(std::ostream& os) {
			os << '{';
			for(int i = 0; i < neg.size(); i++) {
				os << '!' << neg[i] << ((i == neg.size() - 1)? ")" : ", ");
			}
			os << '}';
		}
		
		std::vector<A> get_neg() const {
			return neg;
		}
	
	private:
		std::vector<A> neg;

};

// rezolucija radi sa rezolventom koji ima pozitivnu klauzu
// i onim koji ima sve negativne
// rezultat je Hornova klauza
using HC = std::shared_ptr<HornClause>;
using R1 = std::shared_ptr<Resolvent1>;
using R2 = std::shared_ptr<Resolvent2>;


std::tuple<HC, bool> resolve(const R1& r1, const R2& r2) {
	auto pos = r1->get_pos();
	// sada vadimo redom negativne i pokusavamo da rezolviramo
	// treba potrefiti dva ista prakticno
	
	auto x = r2->get_neg();
	for(auto it = x.begin(); it != x.end(); ++it) {
		if(*it == pos) {
			x.erase(it);
			// eventualno treba dodati negativne iz Resolvent1
			auto t = r1->get_neg();
			x.insert(x.end(), t.begin(), t.end());
			// pravimo query, jer nemamo vise pos
			HC query = std::make_shared<HornQuery>(x);
			return std::tuple<HC, bool>(query, true);
		}
	}
	
	// ne moze da se rezolvira, pa vracamo samo
	return std::tuple<HC, bool>(nullptr, false);
}

bool is_correct(const std::vector<R1>& facts, const R2& query) {
	auto it = facts.begin();
	// pokusavamo da rezolviramo
	// ako smo uspeli, onda menjamo query sa novim
	// i vracamo se na pocetak niza
	// ako smo zaboli praznu klauzu, vracamo false
	// ako smo obisli ceo niz, vracamo true
	auto q = query;
	
	while(it != facts.end()) {
		HC x;
		bool flag;
		std::tie(x, flag) = resolve(*it, q);
		if(flag) {
			auto y = std::dynamic_pointer_cast<HornQuery>(x);
			q = y;
			if(q->get_neg().empty()) return false;
			it = facts.begin();
		} else {
			++it;
		}
	}
	
	return true;

}


int main() {
	
	T const1 = std::make_shared<ConstantTerm>("c1");
	T const2 = std::make_shared<ConstantTerm>("c2");
	std::vector<T> x = {const1, const2};
	T f1 = std::make_shared<FunctionTerm>("f", x);
	
	std::cout << const1 << '\n' << const2 << '\n' << f1 << '\n';
	
	T const3 = std::make_shared<ConstantTerm>("c1");
	std::cout << const3 << '\n' << (const1 == const3) << '\n' << (const1 == f1) << '\n';
	
	std::vector<T> p1_args = {const1, const2, f1};
	A p1 = std::make_shared<Atom>("p", p1_args);
	auto p2_args = p1_args;
	A p2 = std::make_shared<Atom>("p", p2_args);
	std::cout << p1 << '\n' << (p1 == p2) << '\n';
	std::vector<T> q1_args = {const1, const2};
	A q1 = std::make_shared<Atom>("q", q1_args);
	std::cout << q1 << '\n' << (p1 == q1) << '\n';
	
	std::shared_ptr<HornFact> t = std::make_shared<HornFact>(p1);
	std::cout << (*t) << '\n';
	std::vector<A> y_args = {p1, p2};
	std::shared_ptr<HornQuery> y = std::make_shared<HornQuery>(y_args);
	std::vector<A> s_args = {q1};
	std::shared_ptr<HornQuery> s = std::make_shared<HornQuery>(s_args);
	std::cout << *y << '\n';
	HC x1;
	bool x2;
	std::cout << "Rezolviramo:\n";
	std::tie(x1, x2) = resolve(t, y);
	if(x2) {
		std::cout << *x1 << '\n';
	} else {
		std::cout << "Nismo rezolvirali!\n";
	}
	
	std::vector<R1> facts = {t};
	std::cout << is_correct(facts, y) << '\n';
	std::cout << is_correct(facts, s) << '\n';

	return 0;
}
