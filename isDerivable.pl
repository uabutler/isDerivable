/* isDerivable   
 * ===========
 * This program creates a functor, isDerivable/2, that takes two
 * arguments. The first argument is a regular expression, the second
 * is a string, both represented by atoms. If the string can be
 * derived from the regular expression, this functor returns true. 
 * Otherwise, it returns false.
 *
 * As a precondition, it is assumed the regular expression is valid, 
 * and that both the string and the regular expression are defined 
 * only over the alphabet A = {a,b,c}. (Though this can be trivially 
 * modified below.
 *
 * For this program, A + B represents the disjuntion of two regular
 * expression, A and B, AB is the concatenation of A and B, and A*
 * is the closure of A. (A derives an expression repeated 0 or more 
 * times).
 */

/* Authors
 * =======
 * Ulysses Butler
 * Robert Maskek
 * Andrew Flynn
 * Nestor Fong
 */

/*  Base case, since the string will not contain '+' or paran, 
    if this test is true, it means the regex itself is just a
    string */
isDerivable(RegEx, Input) :- RegEx == Input.
/*  It's nessesary to check notDerivable first to prevent infinite
    loops. If you can't derive Input from RegEx, these will all fail,
    which is enough to make the whole functor false */
isDerivable(RegEx, Input) :- not(notDerivable(RegEx, Input)), paran(RegEx, X), isDerivable(X, Input).
/*  This is the base case for star. If star is valid, regardless of
    the output, if the input is empty, the call passes. */
isDerivable(RegEx, Input) :- not(notDerivable(RegEx, Input)), star(RegEx, _), Input == ''.
/*  atom_concat will basically brute force all combinations of 
    concats to make A and B. X is a valid regular expression such 
    that applying a star over it produces RegEx. You then test if you 
    can derive A (the first half) from the version without the star, 
    and send the version with the star back to is derivable. This 
    will likely lead back to these two functors, which will either 
    eventually fail if isDerivable(X, A) ever fails, or will get back 
    to the back case. */
isDerivable(RegEx, Input) :- not(notDerivable(RegEx, Input)), star(RegEx, X), atom_concat(A, B, Input), isDerivable(X, A), isDerivable(RegEx, B).
/*  This is simple, if you can derive the string from either part of 
    the disjuntion, it passes. Otherwise, it fails. */
isDerivable(RegEx, Input) :- not(notDerivable(RegEx, Input)), dis(RegEx, X, Y), (isDerivable(X, Input); isDerivable(Y, Input)).
/*  This also involves a lot of brute forcing. If you can split the 
    string and    the regular expression up into two concatenated parts 
    such that a part of a regular expression can derive its 
    respective part of the string, it passes. Not complicated, but 
    very intensive on the part of the computer */
isDerivable(RegEx, Input) :- not(notDerivable(RegEx, Input)), cat(RegEx, X, Y), atom_concat(A, B, Input), isDerivable(X, A), isDerivable(Y, B).

/*  If the Regular expression gets down to a string concat will 
    eventually bring it down to here where it will fail, and the
    functor call will return false */
notDerivable(RegEx, Input) :- letter(RegEx), RegEx \= Input.

%parentheses
/*  This looks more complicated than it actually is. Basically, it 
    strips paranthesis from boths sides if it can, and returns false 
    if it can't. The match functor is there to ensure the paranthesis 
    being stripped off of the end actually match eachother. ex. 
    (a)(b) -/-> a)(b */
paran(X, Y) :- atom_concat('(', A, X), name(A, B), match(B, 0), atom_concat(Y, ')', A).
/*  This is accomplished by keeping track of the paranthesis we've 
    passed. At first, we've passed zero. As we progress through the 
    string, if we pass an opening paran, we add one, if we pass it's 
    matching closing paran, we subtract one. If we ever go below 
    zero, we've passed a closing paran that wasn't opened, so we 
    return false. If we get to the end, and S != 0, the match is 
    somewhere later, so we've still failed */
match(I, S) :- S == 0, I == [41].
match([H|I], S) :- S >= 0, H == 40, match(I, S + 1).
match([H|I], S) :- H == 41, match(I, S - 1).
match([H|I], S) :- S >= 0, H \= 40, H \= 41, match(I, S).

%0 or more repetitions
/*  Star only applies to a single letter, or a paranthesised regular 
    expression */
star(X, Y) :- atom_concat(Y, '*', X), letter(Y).
star(X, Y) :- atom_concat(Y, '*', X), paran(Y, _).

/*
 *  TODO
 *  ====
 *  Both of these functions are incomplete
 *
 */

%plus sign
/*  This ordering might seem strange, but is nessesary because of 
    Prolog's instantiation. Though it results in a brute force, We 
    need to use X in the first call, since it's the only variable 
    that's been instantiated. */
dis(X, Y, Z) :- atom_concat(A, Z, X), atom_concat(Y, '+', A).
%letters next to each other
/*  This will concatenate a letter or parans to another letter or 
    parans */
    %cat(X, Y, Z) :- atom_concat(Y, Z, X), ((letter(A), atom_concat(_, A, Y)); atom_concat(_, ')', Y)), ((letter(B), atom_concat(B, _, Z)); atom_concat('(', _, Z)).

cat(X, Y, Z) :- atom_concat(Y, Z, X), ((letter(A), atom_concat(_, A, Y)); atom_concat(_, ')', Y); atom_concat(_, '*', Y)), ((letter(B), atom_concat(B, _, Z)); atom_concat('(', _, Z)).

%letters
/* Base cases */
letter('a').
letter('b').
letter('c').
