% a simple grammar to show training workflow
% -cem bozsahin 2017


% verbs  
% good and bad cats, and polysemy for knows.
%   see the comments in the training output for these.

knows v := (s\*np)/^np : \x\y.!know x y;
knows v := (s\*np)/^s : \s\x.!know s x;
knows v := (s\*np)/^np : \x\y.!know y x;    % bad
knows v := (s\*np)/^s : \s\x.!know x s;    % bad

loves v := (s\*np)/^np : \x\y.!love x y;
loves v := (s\*np)/^np : \x\y.!love y x;    % bad

% subjects  and objects -- good and bad type-raised

john n := s/(s\np) : \p.p !john;
john n := s\(s/np) : \p.p !john;  
john n := (s\np)\((s\np)/np) : \p.p !john; 
john n := (s\np)\((s\np)/np) : \p\x.!john p x ; %bad TR lf-wise
mary n := s/(s\np) : \p.p !mary;
mary n := s\(s/np) : \p. p !mary;   
mary n := (s\np)\((s\np)/np) : \p.p !mary;    
mary n := (s\np)\((s\np)/np) : \p\x.!mary p x ; %bad TR lf-wise

% Quinean confusion: syn type is OK but LF is not

john n := s/(s\np) : \p.p !dog;
john n := (s\np)\((s\np)/np) : \p.p !dog;
mary n := s/(s\np) : \p.p !cat;
mary n := (s\np)\((s\np)/np) : \p.p !cat;
