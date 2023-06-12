#include <iostream>
#include <vector>
#include <memory>
#include <map>
#include <string>

struct Term;
using TermPtr = std::shared_ptr<Term>;
using VariableTerm = std::string;
struct FunctionTerm {
	std::string f;
	std::vector<TermPtr> args;

};

struct Term {
	enum Type{
		Variable,
		Function
	} type;
	union {
		VariableTerm var;
		FunctionTerm fun;
	};

	Term(VariableTerm t) : type(Variable), var(t) {}
	Term(FunctionTerm t) : type(Function), fun(t) {}
	~Term() {
		switch(type) {
			case Variable: var.~basic_string();
			case Function: fun.~FunctionTerm();
		
		}
	
	}
}; 

struct AtomData {
	std::string symbol;
	std::vector<TermPtr> args;

};

using Substitution = std::map<std::string, TermPtr>;

TermPtr VariableT(std::string s) { return std::make_shared<Term>(VariableTerm{s}); }
TermPtr FunctionT(std::string s, std::vector<TermPtr> t) {
	return std::make_shared<Term>(FunctionTerm{s, t});
}
AtomData Atom(std::string s, std::vector<TermPtr> argm) { return AtomData{s, argm}; }

TermPtr substitute(TermPtr term, Substitution s){
	switch(term->type) {
	case Term::Variable: return s.find(term->var) != s.end() ? s.at(term->var) : term;
	case Term::Function: 
		std::vector<TermPtr> sub;
		for(auto& t1 : term->fun.args)
			sub.push_back(substitute(t1, s));
		return FunctionT(term->fun.f, sub);
	}
}


AtomData substitute(AtomData atom, Substitution s) {
	AtomData subA(atom);
	for(auto& arg : subA.args) {
		auto x = substitute(arg, s);
		arg.swap(x);
	}
		
	return subA;	
}

bool equal(TermPtr a, TermPtr b) {
	if(a->type != b->type)
		return false;
	switch(a->type) {
	case Term::Variable: return a->var == b->var;
	case Term::Function: {
		if(a->fun.f != b->fun.f)
   			return false;
		if(a->fun.args.size() != b->fun.args.size())
			return false;
		
		/*
		for(auto& arg : a->fun.args)
			for(auto& arg1 : b->fun.args)
				if(!equal(arg, arg1))
					return false;
		*/
		
			// ovako treba
		for(int i = 0; i < a->fun.args.size(); i++) {
			if(!equal(a->fun.args[i], b->fun.args[i])) return false;
		}
		
		return true;	
	}

	}

}

bool equal(AtomData A, AtomData B) {
	if(A.symbol != B.symbol)
		return false;
	if(A.args.size() != B.args.size())
		return false;

	/* nikako ne ovako...
	jer ovako si zapravo proveravala da li su
	svaka dva ista
	for(auto& a : A.args){
		for(auto& b : B.args) {
			if(!equal(a, b))
				return false;
		}
	}
	*/
	
	// ovako treba
	for(int i = 0; i < A.args.size(); i++) {
		if(!equal(A.args[i], B.args[i])) return false;
	}
	
	return true;
}

void print(const TermPtr& t) {
	switch(t->type) {
	case Term::Variable:
		std::cout << t->var;
		return;
	case Term::Function:
		std::cout << t->fun.f << '(';
		for(const auto& a : t->fun.args) {
			print(a);
			std::cout << ", ";
		}
		std::cout << ')';
		return;
	}
}

void print(const AtomData& a) {
	std::cout << a.symbol << '(';
	for(const auto& a : a.args) {
		print(a);
		std::cout << ", ";
	}
	std::cout << ')';
}

bool unify(AtomData A, AtomData B, Substitution s){
	AtomData subA = substitute(A, s);
	AtomData subB = substitute(B, s);
	
	print(subA);
	std::cout << '\n';
	print(subB);
	std::cout << '\n';
	/*
	if(equal(subA, subB))
		return true;
	return false;
	*/
	// cistije je ovako
	return equal(subA, subB);
}



int main() {
	AtomData A = Atom("p", {VariableT("x"), FunctionT("f", {VariableT("x")})});
	AtomData B = Atom("p", {VariableT("y"), FunctionT("f", {VariableT("y")})});

	Substitution s;
	s["x"] = VariableT("y");

	if(unify(A, B, s))
		std::cout << "yes";
	else
		std::cout<< "no";
		

	return 0;

}
