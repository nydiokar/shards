% MMIX Assembly - Shard 0 Hash Ingestion
% The Art of Computer Programming Vol. 1 Fascicle 1
% Donald E. Knuth's MMIX RISC Architecture

        LOC     #100
Main    GETA    $255,Welcome
        TRAP    0,Fputs,StdOut
        
% Gödel number calculation: 2^5 × 3^3 × 5^7
% Using MMIX 64-bit registers
        
        SET     $0,2            % Base prime 2
        SET     $1,5            % Exponent 5
        SET     $2,1            % Result accumulator
        
Power2  BZ      $1,Done2        % If exponent = 0, done
        MUL     $2,$2,$0        % result *= base
        SUB     $1,$1,1         % exponent--
        JMP     Power2
        
Done2   SET     $3,$2           % Save 2^5 = 32
        
        SET     $0,3            % Base prime 3
        SET     $1,3            % Exponent 3
        SET     $2,1
        
Power3  BZ      $1,Done3
        MUL     $2,$2,$0
        SUB     $1,$1,1
        JMP     Power3
        
Done3   MUL     $3,$3,$2        % 32 × 27 = 864
        
        SET     $0,5            % Base prime 5
        SET     $1,7            % Exponent 7
        SET     $2,1
        
Power5  BZ      $1,Done5
        MUL     $2,$2,$0
        SUB     $1,$1,1
        JMP     Power5
        
Done5   MUL     $3,$3,$2        % 864 × 78125 = 67,500,000
        
% Print result
        GETA    $255,Result
        TRAP    0,Fputs,StdOut
        
        SET     $255,$3
        GETA    $0,Buffer
        TRAP    0,Sprintf,$0
        
        GETA    $255,Buffer
        TRAP    0,Fputs,StdOut
        
        TRAP    0,Halt,0

Welcome BYTE    "MMIX Shard 0 - CICADA-71 Level 0",10,0
Result  BYTE    "Gödel number: ",0
Buffer  OCTA    0,0,0,0
