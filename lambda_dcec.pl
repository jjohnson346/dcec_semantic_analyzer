%% lambda_dcec.pl

%% This module uses the lambda calculus to generate semantic representations
%% in the DCEC.

%% The lambda calculus is discussed by the authors, Blackburn and Bos,
%% as being a notational extension of FOL.  However, I think it's better for the
%% purposes of what we're doing here to think of it as an intermediate language
%% into which we translate a natural language expression using a DCG. Then, once
%% the expression is in the language of the lambda calculus, we can translate
%% the expresssion into FOL (and in this case, DCEC)  using beta conversion
%% (the processing of functional applications).  The process is as follows:
%%
%% natural language expression ---> DCG ---> lambda calculus expression --->
%%
%% ----> beta conversion ----> DCEC/FOL formula
%%
%% Under this approach, individual words of the lexicon have semantic
%% representations that are lambda calculus abstractions, and their meanings
%% are glued together using grammar rules that apply functional applications, as
%% the term is defined in Blackburn and Bos.

%% The advantages of using the lambda calculus over the direct method (as used
%% in example 1) are threefold, based on my observations:

%% 1. semantic representations of words are localized to the lexicon rules (and
%% not mixed into the grammar rules as they were in the direct method).  Besides
%% the inherent advantage of consistency this provides, a fortunate byproduct is that
%% there isn't duplication of grammar rules with the addition of lexical entries.
%% 2.  Because of item 1, this approach is much more scalable to a larger lexicon/
%% subset of natural language than the direct method.
%% 3.  semantic representations are built up compositionally from the words of
%% the natural language expressions, consistent with the spirit
%% of computational semantics - the meaning of a phrase is based on the combined meanings
%% of the words that make up that phrase.

%% usage for this file:

%% 1.  navigate to the directory that contains this file.
%% 2.  start swipl prolog.
%% 3.  execute [lambda_dcec]. to load this kb.
%% 4.  follow the instructions as listed in the menu.
%% 5.  the exemplar sentence for this demo code:
%%
%% Alice sees that in the beginning, bob places the cookie in the cabinet.

:- use_module(betaConvert,[betaConvert/2]).
:- use_module(readLine,[readLine/1]).
:- use_module(comsemPredicates,[printRepresentations/1]).

lambdaDCEC:-
	readLine(Sentence),
        lambdaDCEC(Sentence,DCECs),
	printRepresentations(DCECs).

lambdaDCEC(Sentence,ValidDCECs):-
    setof(DCEC,t(Sentence,DCEC),DCECs),
    validSems(DCECs,ValidDCECs).

%% lambdaDCEC(Sentence,DCECs) :-
%%     setof(DCEC,t(Sentence,DCEC),DCECs).

validSems([],[]).
validSems([SemsH|SemsT],[SemsH|ValidSemsT]) :-
    validSem(SemsH),
    !,
    validSems(SemsT,ValidSemsT).
validSems([SemsH|SemsT],ValidSemsT) :-
    \+ validSem(SemsH),
    !,
    validSems(SemsT,ValidSemsT).
	   
validSem(DCEC) :-
    =..(DCEC,[DCEC|[]]),!.
validSem(DCEC) :-
    =..(DCEC,[Functor|DCECT]),
    Functor \== lam,
    Functor \== app,
    validSems(DCECT).

validSems([]) :- !.
validSems([DCECH|DCECT]) :-
    validSem(DCECH),
    validSems(DCECT).



t(Sentence,CEC) :-
    s(Sem,Sentence,[]),
    betaConvert(Sem,CEC),
    numbervars(CEC,23,_).

%% grammar

s(app(NP,VP)) --> np(NP),vp(VP).

%% sentence with intro temporal phrase. (e.g., in the beginning, mia walked home.)
s(app(TP,S)) --> tp(TP),s(S).

%% epistemic/doxastic operators - knows, believes, sees
s(app(NP,EP)) --> np(NP),ep(EP).

%% epistemic operator - common knowledge
s(app(CKEPOP,S)) --> ckepop(CKEPOP),s(S).

np(PN) --> pn(PN).                           % proper noun
np(app(IART,Noun)) --> iart(IART),noun(Noun).   % determiner + noun 
np(Noun) --> dart,noun(Noun).

vp(IV) --> iv(IV).
vp(app(TV,NP)) --> tv(TV),np(NP).
vp(app(app(TV,NP1),PP)) --> tv(TV),np(NP1),pp(PP).
vp(app(app(TV,NP1),TP)) --> tv(TV),np(NP1),tp(TP).
vp(ADJ) --> lv,adj(ADJ).
%% to do: convert dtv's to handle events.
%%vp(app(app(DTV,NP1),NP2)) --> dtv(DTV),np(NP1),np(NP2).

pp(NP) --> prep,np(NP).

%% tp(TN) --> prep(_),tn(TN).
tp(TN) --> prep,dart,tn(TN).
tp(TN) --> tn(TN).

%% epistemic operator phrases, such as
%% those beginning with knows, believes,
%% sees, etc.
%% note:  for justification for this combination
%% scheme for epop and s, see notes dated
%% 02/13/2018 re: example - julia believes mia walks.
ep(app(EPOP,lam(C,app(C,S)))) --> epop(EPOP),s(S). 



%% lexicon

%% non-proper nouns, used with indefinite article (a, every)
noun(lam(X,woman(X))) --> [woman].
noun(lam(X,man(X))) --> [man].
noun(lam(X,ball(X))) --> [ball].
noun(lam(X,car(X))) --> [car].

%% non-proper nouns, used with definite article (the, this, etc.)
noun(lam(X,app(X,ball))) --> [ball].
noun(lam(X,app(X,cookie))) --> [cookie].
noun(lam(X,app(X,cabinet))) --> [cabinet].
noun(lam(X,app(X,rent))) --> [rent].
noun(lam(X,app(X,car))) --> [car].

%% time nouns, used with definite article (the, this, etc.)
tn(lam(X,app(X,beginning))) --> [beginning].
tn(lam(X,app(X,yesterday))) --> [yesterday].
tn(lam(X,app(X,tomorrow))) --> [tomorrow].


%% proper nouns
pn(lam(X,app(X,vincent))) --> [vincent].
pn(lam(X,app(X,mia))) --> [mia].
pn(lam(X,app(X,johnny))) --> [johnny].
pn(lam(X,app(X,billy))) --> [billy].
pn(lam(X,app(X,caroline))) --> [caroline].
pn(lam(X,app(X,julia))) --> [julia].
pn(lam(X,app(X,bob))) --> [bob].
pn(lam(X,app(X,alice))) --> [alice].

%% adjectives
adj(lam(X,red(X))) --> [red].

%% intransitive verbs
iv(lam(X,walk(X))) --> [walks].
iv(lam(X,dance(X))) --> [dances].

%% linking verbs
lv --> [is].

%% transitive verbs - actions are treated as events.
%% therefore, semantic representation of verb is often
%% expressed in terms of the event calculus.

%% making sense of all the lambdas/apps in these transitive verb semantic representations:
%% consider the following example expression
%% as it relates to the semantic representation of the word, places (the trans. verb):
%%
%%       in the beginning bob places the cookie in the cabinet.
%%
%% Those sentence elements coming after the word, places, must have a lam/variable expression
%% at the beginning of the semantic representation with a subsequent substitution
%% in an app/variable(lam/new variable complex) expression down the line in the
%% representation.  For example, the noun phrase, the cookie, succeeds 
%% the verb, places, in the sentence. The semantic representation for "the cookie"
%% is mapped to the lam(X,_) variable, where X appears in the following expression
%% with app(X,lam(Z,_).  This has the effect of placing
%% the sem. rep. for "the cookie" precisely in the position occupied by variable, Z.
%% Likewise, "in the cabinet"'s semantic representation is mapped to the lam(M,_)
%% expression, where there is an app(M,lam(N,_) expression therein.  This effectively places
%% the semantic representation for "in the cabinet" where the variable N is located.
%% On the other hand, for the noun phrase, bob, which *precedes* the verb, places, 
%% that element is mapped to the lam(Y,_) expression and is substituted for the variable, Y.

tv(lam(X,lam(M,lam(Y,lam(W,app(M,lam(N,app(X,lam(Z,happens(action(Y,places(Z,N)),W)))))))))) --> [places].
tv(lam(X,lam(P,lam(Y,app(P,lam(W,app(X,lam(Z,happens(action(Y,pay(Z),W)))))))))) --> [paid].
tv(lam(X,lam(P,lam(Y,app(P,lam(W,app(X,lam(Z,happens(action(Y,sell(Z)),W))))))))) --> [will,sell].
%% to do: convert the loves semantic representation to handle event syntax.
%% tv(lam(X,lam(Y,app(X,lam(Z,love(Y,Z)))))) --> [loves].

%% ditransitive verbs
%% to do: convert dtv's to handle event syntax.
%% dtv(lam(X,lam(M,lam(Y,app(M,lam(N,app(X,lam(Z,offer(Y,N,Z))))))))) --> [offers].
%% dtv(lam(X,lam(M,lam(Y,app(M,lam(N,app(X,lam(Z,throw(Y,N,Z))))))))) --> [throws].

%% prep(in) --> [in].
prep --> [in].

%% epistemic operators
%% support the dcec.
epop(lam(X,lam(Y,app(X,lam(Z,'K'(Y,Z)))))) --> [knows].
epop(lam(X,lam(Y,app(X,lam(Z,'K'(Y,Z)))))) --> [knows,that].
epop(lam(X,lam(Y,app(X,lam(Z,'B'(Y,Z)))))) --> [believes].
epop(lam(X,lam(Y,app(X,lam(Z,'B'(Y,Z)))))) --> [believes,that].
epop(lam(X,lam(Y,app(X,lam(Z,'S'(Y,Z)))))) --> [sees].
epop(lam(X,lam(Y,app(X,lam(Z,'S'(Y,Z)))))) --> [sees,that].

%% epistemic operator
%% common knowledge
ckepop(lam(X,'C'(X))) --> [it,is,common,knowledge,that].
ckepop(lam(X,'C'(X))) --> [everyone,knows].
ckepop(lam(X,'C'(X))) --> [everyone,knows,that].

%% determiners
%% indefinite articles
iart(lam(U,lam(V,all(X,imp(app(U,X),app(V,X)))))) --> [every].
iart(lam(U,lam(V,some(X,and(app(U,X),app(V,X)))))) --> [a].

%% definite articles
%% notice that there is no semantic representation for the definite article.
%% This is due to the fact that when the definite article is combined with
%% a noun to form a noun phrase, the noun phrase's semantic representation
%% should simply be that of the noun, itself, (with no contribution from
%% the definite article).  See the np --> dart, noun rule, above.
dart --> [the].




/*========================================================================
   Info
========================================================================*/

info:-
   format('~n> ------------------------------------------------------------------ <',[]),
   format('~n> lambda_dcec.pl, by Joe Johnson                                     <',[]),
   format('~n>                                                                    <',[]),
   format('~n> acknowledgements are owed to  Blackburn, Ros (2006) Representation <',[]),
   format('~n> and Inference in Natural Language which inpired the lambda-calulus <',[]),
   format('~n> based approach adopted in this system and which provided supporting<',[]),
   format('~n> utility predicates that were leveraged significantly.              <',[]),
   format('~n>                                                                    <',[]),
   format('~n> ?- lambdaDCEC.          - parse a typed-in sentence                <',[]),
   format('~n> ?- lambdaDCEC(S,F)      - parse a sentence and return formula      <',[]),
   format('~n> ?- s(Sem,S,[]).         - produce lambda calc formula for sentence <',[]),
   format('~n>                           input as list                            <',[]),
   format('~n> ?- vp(Sem,VP,[])        - produce lambda calc formula for verb     <',[]),
   format('~n>                           phrase input as list                     <',[]),
   format('~n> ?- info.                - shows this information                   <',[]),
   format('~n> ------------------------------------------------------------------ <',[]),
   format('~n~n',[]).


/*========================================================================
   Display info at start
========================================================================*/

:- info.
