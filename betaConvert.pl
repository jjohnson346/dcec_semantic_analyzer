%% betaConvert.pl
%% This module contains the implementation for the
%% betaConvert prediate.

:- module(betaConvert,[betaConvert/2]).

:- use_module(alphaConvert,[alphaConvert/2]).


%% initial beta conversion predicate
betaConvert(Expression,Result) :-
    betaConvert(Expression,Result,[]).


%% for tracing
%% betaConvert(X,_,S) :-
%%     nl, write('Expression: '), write(X),
%%     nl, write('Stack: '), write(S),
%%     fail.

%% beta conversion when the expression
%% is just a variable.
betaConvert(X,Y,[]) :- var(X), Y=X.


%% beta conversion when we have an application
%% (app lambda calculus expression)
%% and the functor is not a variable.
betaConvert(Expression,Result,Stack) :-
    nonvar(Expression),
    Expression = app(Functor,Argument),
    nonvar(Functor),
    alphaConvert(Functor,ConvertedFunctor),
    betaConvert(ConvertedFunctor,Result,[Argument|Stack]).

%% beta conversion when we have an abstraction
%% (lam lambda calculus expression)
betaConvert(Expression,Result,[X|Stack]) :-
    nonvar(Expression),
    Expression = lam(X,Formula),
    betaConvert(Formula,Result,Stack).

%% beta conversion when we have a complex expression
%% (such as conjunction) but the stack is empty.
%% This also serves to handle the base case for
%% beta convert, handling an expression containing
%% an atomic expression as a list with a single
%% element.
betaConvert(Expression,Result,[]) :-
    nonvar(Expression),
\+((Expression = app(X,_), nonvar(X))),
compose(Expression,Functor,SubExpressions),
betaConvertList(SubExpressions,ResultSubExpressions),
compose(Result,Functor,ResultSubExpressions).

%% betaConvertList/2 handles beta conversion for a
%% list of expressions, called by betaConvert predicate
%% for the case in which we have a complex
%% lambda calculus expression consisting of
%% 2 or sub-expressions.

betaConvertList([],[]).

betaConvertList([Expression|Others],[Result|Results]) :-
    betaConvert(Expression,Result),
    betaConvertList(Others,Results).


%% compose/3 is available in comSemPredicates.pl,
%% but it is reproduced here so that it is
%% not necessary to import it.
compose(Term,Functor,Arguments) :-
    =..(Term,[Functor|Arguments]).



