{ @author: Sylvain Maltais (support@gladir.com)
  @source: Bas‚ sur le livre "Compiler Construction" de Niklaus Wirth's
  @created: 2023
  @website(https://www.gladir.com/CODER/OBERON-TP)
  @abstract(Target: Turbo Pascal 7, Free Pascal 3.2)
}

Unit RISC;

INTERFACE

Uses CRT;

Const
 opMOV=0;
 opLSL=1;
 opASR=2;
 opROR=3;
 opAND=4;
 opANN=5;
 opIOR=6;
 opXOR=7;
 opADD=8;
 opSUB=9;
 opMUL=10;
 opDIV=11;

Var
 IR:LongInt;   (* Registre d'instructions *)
 PC:LongInt;   (* Compteur de programme *)
 N,Z:Boolean;  (* Drapeau de condition *)
 R:Array[0..16]of LongInt;
 H:LongInt;    (* Registre aux pour la division*)

Procedure Execute(Var M:Array of LongInt;Size,PC:LongInt);

IMPLEMENTATION

Procedure Execute(Var M:Array of LongInt;Size,PC:LongInt);
Var
 a,b,op,im:LongInt;  (* Champs d'instruction *)
 adr,A_,B_,C_:LongInt;
Begin
 PC:=0;
 R[13]:=PC*4;
 R[14]:=Size*4;
 Repeat
  IR:=M[PC];
  Inc(PC);
  If PC>Size Then Break;
  a:=(IR shr 24) and $F;
  b:=(IR shr 20) and $F;
  op:=(IR shr 16) and $F;
  im:=IR and $FFFF;
  If Not(Odd(IR DIV $80000000))Then Begin
   B_:=R[b];
   If Not(Odd(IR DIV $40000000))Then C_:=R[IR and $F] Else
   If Not(Odd(IR DIV $10000000))Then C_:=im
    Else
   Begin
    C_:=im or LongInt($FFFF0000);
   End;
   Case op Of
    opMOV:Begin
     If not(Odd(IR DIV $20000000))Then Begin
      A_:=C_
     End
      Else
     Begin
      A_:=H;
     End;
    End;
    opLSL:A_:=B_ shl C_;
    opASR:A_:=B_ shr C_;
    opROR:A_:=(B_ shr C_)or(B_ shl (32 - C_));
    opAND:A_:=B_ and  C_;
    opANN:A_:=B_ and Not C_;
    opIOR:A_:=B_ or C_;
    opXOR:A_:=B_ xor C_;
    opADD:A_:=B_+C_;
    opSUB:A_:=B_-C_;
    opMUL:A_:=B_*C_;
    opDIV:Begin
     A_:=B_ div C_;
     H:=B_ mod C_;
    End;
   End;
   R[a]:=A_;
   N:=A_<0;
   Z:=A_=0;
  End
   Else
  If Not(Odd(IR div $40000000))Then Begin
   adr:=(R[b]+IR mod $100000) div 4;
   If Not(Odd(IR div $20000000))Then Begin
    IF adr>=0 Then Begin
     R[a]:=M[adr];
     N:=A_<0;
     Z:=A_=0;
    End
     Else
    IF adr=-1 Then Read(R[a]) Else
    IF adr=-2 Then Z:=Not(KeyPressed);
   End
    Else
   Begin
    If adr>=0 Then M[adr]:=R[a] Else
    If adr=-1 Then Write(R[a]:4) Else
    If adr=-2 Then WriteLn;
   End;
  End
   Else
  Begin
   If(a=0)and N or
     (a=1)and Z or
     (a=5)and N or
     (a=6)and(N or Z)or
     (a=7)or
     (a=8)and not N or
     (a=9)and not Z or
     (a=13)and not N or
     (a=14)and not (N or Z)Then Begin
    If Odd(IR div $10000000)Then Begin
     R[15]:=PC*4;
    End;
    IF Odd(IR div $20000000)Then Begin
     PC:=(PC+(IR MOD $1000000)) MOD $40000;
    End
     Else
    Begin
     PC:=R[IR MOD $10] DIV 4;
    End;
   End;
  End;
 Until(PC=0);
End;

BEGIN
 (* Initialise le module RISC *)
 FillChar(R,SizeOf(R),0);
 PC:=0;
 N:=False;
 Z:=False;
 H:=0;
 IR:=0;
END.
