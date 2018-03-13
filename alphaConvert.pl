%% alphaConvert.pl
%% This module contains the alphaConvert predicate which switches
%% variable names in order to prevent variable naming
%% conflicts when arguments are applied to functors.  When the name
%% of a free variable in an argument is the same as that of a
%% bound variable in a functor, we have a naming collision that
%% can have bad results.  So, we switch the names of the bound
%% variables in the functors to prevent this.  (bound by exists and
%% for all quantifiers, as well as lambda quantifier).
:- module(alphaConvert,[alphaConvert/2,
			alphaConvert/4]).

:- use_module(comsemPredicates,[memberList/2,compose/3]).

%% alphaConvert/2
%% base call to alphaConvert, which expands the call from 2 args
%% to 4 args, including 2 additional args for administering a
%% variable substitutions list and a difference list of free
%% variables.
alphaConvert(Expression,Converted) :-
    alphaConvert(Expression,[],[]-_,Converted).

%% if the expression, assigned to X, is a variable, then there
%% are two possibilities:
%% 1.  the variable is a quantified variable for which we've
%%     already created a substitution (see the clauses below
%%     for handling the quantified variable situation).  In
%%     this case, we make the substitution, leave the free vars
%%     difference list alone and move on.
%% 2.  the variable is not a quantified variable, and thus, it is
%%     necessarily a free variable, which needs to be added to the
%%     list of free variables (implemented using a difference list
%%     pair).  We maintain a list of these free variables so that
%%     when a new variable must be created due to a new quant.
%%     expression, the new variable is distinct from all quantified
%%     and free variables encountered previously.
alphaConvert(X,Sub,Free1-Free2,Y) :-
    var(X),
    (
	memberList(sub(Z,Y),Sub),
	X==Z, !,
	Free2=Free1
     ;
     Y=X,
     Free2=[X|Free1]
    ).


%% if Expression is a quantified expression (exists, forall, lambda),
%% then substitute the variable in the expression with a brand
%% new variable.  The clauses below introduce a new variable by
%% exploiting the prolog feature that a new variable in this clause
%% will trigger the creation of a brand new variable, not one
%% used in a prior application of this clause of the predicate. So,
%% sitching to a new variable really makes the variable *brand* new.
alphaConvert(Expression,Subs,Free1-Free2,some(Y,F2)) :-
    nonvar(Expression),
    Expression = some(X,F1),
    alphaConvert(F1,[sub(X,Y)|Subs],Free1-Free2,F2).
     
alphaConvert(Expression,Subs,Free1-Free2,all(Y,F2)) :-
    nonvar(Expression),
    Expression = all(X,F1),
    alphaConvert(F1,[sub(X,Y)|Subs],Free1-Free2,F2).

alphaConvert(Expression,Subs,Free1-Free2,lam(Y,F2)) :-
    nonvar(Expression),
    Expression = lam(X,F1),
    alphaConvert(F1,[sub(X,Y)|Subs],Free1-Free2,F2).


%% handle complex expression, but those that are not prefixed
%% by a quantifier.  for example, this clause of the predicate
%% handles the case, forall(x):woman(x) - specifically, the woman(x)
%% part of the formula.  forall(x)... would be handled by the
%% clause that handles forall quantifier expressions, but then
%% there's a recursive call into this clause to handle the woman(x)
%% portion.
alphaConvert(F1,Subs,Free1-Free2,F2) :-
    nonvar(F1),
\+ F1=some(_,_),
\+ F1=all(_,_),
\+ F1=lam(_,_),
compose(F1,Symbol,Args1),
alphaConvertList(Args1,Subs,Free1-Free2,Args2),
compose(F2,Symbol,Args2).


%% handle each formula in a list, using the same approach as
%% that used in betaConvert.
alphaConvertList([],_,Free-Free,[]).
alphaConvertList([Arg1|Args1],Subs,Free1-Free3,[Arg2|Args2]) :-
    alphaConvert(Arg1,Subs,Free1-Free2,Arg2),
    alphaConvertList(Args1,Subs,Free2-Free3,Args2).




