% (~b => (a = > b))
% (b | (a => b))
% b | (~a | b)
% b | ~a

% ~b => (a | b)
% b | a | b
% b | a

% (b | ~a) & (b | a) => b
% !(b | ~a) | !(b | a) | b
% (~b & a) | (~b & ~a) | b
% b = 1 --> xxx | 1 --> 1
% b = 0 --> a | ~a | 0 --> 1

fof(f, conjecture, ( ( (~b) => (a => b) ) & ( (~b)  =>  (a | b) )  ) => b).
