usage: python .\nfa-builder.py alphabet_file

-----------------------------------

Input format for the alphabet:

a
b
c
last

---------------------------------------

Input format for the LTLf formula:

a and b 
a or b
X (a) = next
WX (a) = weak next
G (a) = globally
(a) U (b) = until
(a) R (b) = weak until
not a

-----------------------------------------

Input format for the sequence of fluents:

a,c		#F1
a,b,c		#F2
c		#F3
c,last		#F4

Notice that the order of the alphabet IS RELEVANT for the sequence of fluents! It has to be maintained

e.g.  c,a instead of a,c is wrong! It rises a key error

Correct combinations for the alphabet above:

a,b,c,last
a,last
b,c,last
last
a,b
....

Wrong combinations:

b,a
last,b
c,last,a
c,b,a
c,a,b
.....

When a fluent is not present, it means that is false. True otherwise.

-------------------------------------------------------------------------------
