{ @author: Sylvain Maltais (support@gladir.com)
  @source: BasÇ sur le livre "Compiler Construction" de Niklaus Wirth's
  @created: 2023
  @website(https://www.gladir.com/CODER/OBERON-TP)
  @abstract(Target: Turbo Pascal 7, Free Pascal 3.2)
}

Unit OSG;

INTERFACE

Uses OSS;

Const
 MemSize = 8192;

  (* Registres rÇservÇs *)
 SB=13;
 SP=14;
 LNK=15;

  (* Code opcodes frÇquemment utilisÇ *)
 U=$2000;
 opMov=0;
 opLSL=1;
 opASR=2;
 opROR=3;
 opAnd=4;
 opANN=5;
 opIOR=6;
 opXor=7;
 opAdd=8;
 opSUB=9;
 opCMP=9;
 Mul=10;
 opDiv=11;
 LDW=0;
 STW=2;
 BR=0;
 BLR=1;
 BC=2;
 BL=3;
 MI=0;
 PL=8;
 EQ=1;
 NE=9;
 LT=5;
 GE=13;
 LE=6;
 GT=14;

Type
 ModeClassType=(mcHead,mcConst,mcVar,mcPar,mcFld,mcTyp,mcSProc,
                mcSFunc,mcProc,mcNoTyp,mcReg,mcRegI,mcCond);

 ObjectPtr=^ObjDesc;
 TypePtr=^TypeDesc;

 Item=Record
  Mode:ModeClassType;
  Lev:Integer;
  Type_:TypePtr;
  a,b,r:LongInt;
 End;

 ObjDescPtr=^ObjDesc;

 ObjDesc=Record
  Class_:ModeClassType;
  Lev:Integer;
  Next,Dsc:ObjectPtr;
  PType:TypePtr;
  Name:OSS.Ident;
  Val,NofPar:LongInt;
 End;

 TypeDesc=Record
  DataType:(BooleanDataType,IntegerDataType,ArrayDataType,RecordDataType);
  Dsc:ObjectPtr;
  Base:TypePtr;
  Size,Len,NofPar:LongInt;
 End;

Var
 boolType,intType:TypePtr;
 curlev,PC:Integer;
 entry:LongInt;
 RH:LongInt; (* Registre de pointeur de pile *)
 relmap:Array[0..6] of Integer;
 Code:Array[0..MemSize] of LongInt;
 mnemo0,mnemo1:Array[0..16] of String[4]; (* Pour le decodeur *)

Procedure AddOp(op:LongInt;Var x,y:Item);
Procedure And1(var x: Item);
Procedure And2(Var x,y:Item);
Procedure BJump(L:LongInt);
Procedure Call(Var Obj:ObjectPtr);
Procedure CBJump(Var x:Item;L:LongInt);
Procedure CFJump(Var x:Item);
Procedure CheckRegs;
Procedure Close;
Procedure Decode;
Procedure DivOp(Op:Longint;Var x,y:Item);
Procedure Enter(ParBlkSize,LocBlkSize:LongInt);
Procedure Eot(Var x:Item);
Procedure Execute;
Procedure Field(Var x:Item; y:ObjectPtr);
Procedure Fix(_At,WithVal:LongInt);
Procedure FixLink(L:LongInt);
Procedure FJump(Var L:LongInt);
Procedure Header(size:LongInt);
Procedure IncLevel(n:Integer);
Procedure IncR;
Procedure Index(Var x,y:Item);
Procedure Load(Var x:Item);
Procedure LoadAdr(Var x:Item);
Procedure LoadCond(Var X:Item);
Procedure MakeConstItem(Var x:Item;Typ:TypePtr;Val:LongInt);
Procedure MakeItem(Var x:Item; y:ObjectPtr;CurLev:LongInt);
Function  Merged(L0,L1:LongInt):LongInt;
Procedure MulOp(Var x,y:Item);
Procedure Neg(Var x:Item);
Function  Negated(Cond:LongInt):LongInt;
Procedure Not_(Var x:Item);
Procedure Open;
Procedure OpenArrayParam(Var x:Item);
Procedure Or1(Var x:Item);
Procedure Or2(Var x,y:Item);
Procedure Ord(Var x:Item);
Procedure Put0(op,a,b,c:LongInt);
Procedure Put1(op,a,b,im:LongInt);
Procedure Put2(op,a,b,off:LongInt);
Procedure Put3(op,cond,off:LongInt);
Procedure ReadInt(Var x:Item);
Procedure Relation(op:Integer;Var x,y:Item);
Procedure Return(size:LongInt);
Procedure SetCC(Var X:Item;N:LongInt);
Procedure Store(Var x,y:Item);
Procedure TestRange(x:LongInt);
Procedure ValueParam(Var x:Item);
Procedure VarParam(Var x:Item;ftype:TypePtr);
Procedure WriteChar(Var x:Item);
Procedure WriteInt(Var x:Item);
Procedure WriteLine;

IMPLEMENTATION

Uses RISC;

Function ByteHex2Str(value:Byte):String;
Const
 matrix:Array[0..15]of Char = ('0','1','2','3','4','5','6','7','8','9','A','B','C','D','E','F');
Begin
 ByteHex2Str:=matrix[(value shr 4) and $0F]+matrix[value and $F];
End;

Function HexWord2Str(value:Word):String;Begin
 HexWord2Str:=ByteHex2Str(Hi(value))+ByteHex2Str(Lo(value));
End;

Function LongHex2Str(value:LongInt):String;
Begin
 LongHex2Str:=ByteHex2Str((value shr 24)and $FF)+
              ByteHex2Str((value shr 16)and $FF)+
              ByteHex2Str((value shr 8)and $FF)+
              ByteHex2Str(value and $FF);
End;

Procedure Put0(op,a,b,c:LongInt);Begin
 (* êmettre une instruction au format 0 *)
 Code[pc]:=((((a shl 4) + b) shl 4 + op) shl 16)+c;
 Inc(pc);
End;

Procedure Put1(op,a,b,im:LongInt);Begin
 (* êmettre une instruction au format 1 *)
 If im<0 Then op:=op+$1000; (* Fixe le bit v *)
 Code[pc]:=((((((a+$40)shl 4)+b) shl 4)+op) shl 16)+(im mod $10000);
 Inc(pc);
End;

Procedure Put2(op,a,b,off:LongInt);Begin
  (* êmettre une instruction de chargement ou d'entreposage *)
 Code[pc]:=(((((op+8)shl 4)+a)shl 4+b)shl 20)+(off mod $10000);
 Inc(pc);
End;

Procedure Put3(op,cond,off:LongInt);Begin
  (* êmettre une instruction de branchement *)
 Code[PC]:=((((Op+12) shl 4)+Cond) shl 24)+(Off mod $1000000);
 Inc(pc);
End;

Procedure IncR;Begin
 If RH < SB Then Inc(RH)
            Else OSS.Mark('DÇbordement de la pile du registre');
End;

Procedure CheckRegs;Begin
 If RH<>0 Then Begin
  OSS.Mark('Pile de registre');
  RH:=0;
 End;
End;

Procedure SetCC(Var X:Item;N:LongInt);Begin
 x.mode:=mcCond;
 x.a:=0;
 x.b:=0;
 x.r:=N;
End;

Procedure TestRange(x:LongInt);Begin
  (* EntitÇ de 16 bits *)
 If(x>$FFFF)or(x<-$10000)Then OSS.Mark('Valeur trop large');
End;

Function Negated(Cond:LongInt):LongInt;Begin
 If cond<8 Then Cond:=Cond+8
           Else Cond:=Cond-8;
 Negated:=Cond;
End;

Procedure Fix(_At,WithVal:LongInt);Begin
 Code[_At]:=Code[_At] div $1000000 * $1000000 + (withVal mod $1000000);
End;

Procedure FixLink(L:LongInt);
Var
  L1:LongInt;
Begin
 While L<>0 do Begin
  If L<MemSize Then Begin
   L1:=Code[L] mod $4000;
   fix(L,pc-L-1);
   L:=L1;
  End;
 End;
End;

Procedure Load(Var x:Item);Begin
 If x.mode <> mcReg Then Begin
  If x.mode=mcVar Then Begin
   If x.r>0Then Put2(Ldw, RH, SP, x.a) (* local *)
           Else Put2(Ldw, RH, SB, x.a);
   x.r := RH;
   IncR;
  End
   Else
  If x.mode=mcPar Then Begin
   Put2(Ldw,RH,SP,x.a);
   Put2(Ldw,RH,RH,x.b);
   x.r:=RH;
   IncR;
  End
   Else
  If x.mode=mcConst Then Begin
   If(x.a >= $10000) or (x.a < -$10000)Then OSS.Mark('Constante trop large');
   Put1(opMov, RH, 0, x.a);
   x.r:=RH;
   IncR;
  End
   Else
  If x.mode=mcRegI Then Put2(Ldw,x.r,x.r,x.a) Else
  If x.mode=mcCond Then Begin
   Put3(2,Negated(x.r), 2);
   FixLink(x.b);
   Put1(opMov,RH,0,1);
   Put3(2,7,1);
   FixLink(x.a);
   Put1(opMov,RH,0,0);
   x.r:=RH;
   incR;
  End;
  x.mode:=mcReg;
 End;
End;

Procedure LoadAdr(Var x:Item);Begin
 If x.mode=mcVar Then Begin
  If x.r>0 Then Put1(opAdd, RH, SP, x.a);     (* local *)
   x.r:=RH;
   IncR;
  End
   Else
  If x.mode=mcPar Then Begin
   Put2(Ldw,RH,SP,x.a);
   Put1(opAdd,RH,RH,x.b);
   x.r:=RH;
   IncR;
 End
  Else
 If(x.mode=mcRegI)and(x.a<>0)Then Begin
  Put1(opAdd, x.r, x.r, x.a);
 End
  Else
 Begin
  OSS.Mark('Erreur d''adresse');
 End;
 x.mode := mcReg;
End;

Procedure LoadCond(Var X:Item);Begin
 If X.Type_^.DataType=BooleanDataType Then Begin
  If X.Mode=mcConst Then x.r:=15-x.a*8
   Else
  Begin
   Load(x);
   Put1(opCMP,x.r,x.r,0);
   x.r:=NE;
   Dec(RH);
  End;
  x.mode:=mcCond;
  x.a:=0;
  x.b:=0;
 End
  Else
 OSS.Mark('Ce n''est pas un boolÇan');
End;

Function Merged(L0,L1:LongInt):LongInt;
Var
 L2,L3:LongInt;
Begin
 If L0<>0 Then Begin
  L3:=L0;
  Repeat
   L2:=L3;
   L3:=Code[L2] mod $4000;
  Until L3=0;
  Code[L2]:=Code[L2]+L1;
  L1:=L0;
 End;
 Merged:=L1;
End;

Procedure IncLevel(n:Integer);Begin
 CurLev:=CurLev+n;
End;

Procedure MakeConstItem(Var x:Item;Typ:TypePtr;Val:LongInt);Begin
 x.mode:=mcConst;
 x.Type_:=Typ;
 x.a:=Val;
End;

Procedure MakeItem(Var x:Item; y:ObjectPtr;CurLev:LongInt);Begin
 x.mode:=y^.class_;
 x.Type_:=y^.PType;
 x.a:=y^.Val;
 x.r:=y^.lev;
 If y^.class_ = mcPar Then x.b:=0;
 If (y^.lev>0) and (y^.lev <> curlev)and(y^.class_<>mcConst)Then OSS.Mark('Erreur de niveau');
End;

Procedure Field(Var x:Item; y:ObjectPtr);Begin
 If(x.mode=mcVar)or(x.mode=mcRegI)Then x.a:=x.a+y^.val Else
 If x.mode=mcPar Then Begin
  Put2(Ldw, RH, x.r, x.a);
  x.mode:=mcRegI;
  x.r:=RH;
  x.a:=y^ .val;
  incR;
 End;
End;

Procedure Index(Var x,y:Item);
Var
 s:LongInt;
Begin
 If y.mode=mcConst Then Begin
  If(y.a<0)or(y.a>=x.type_^.len)Then OSS.Mark('Mauvaise index');
  If x.mode=mcPar Then Begin
   Put2(Ldw, RH, x.r, x.a);
   x.mode:=mcRegI;
   x.a:=0;
  End;
  x.a:=x.a+y.a*x.type_^.base^.Size;
 End
  Else
 Begin
  s:=x.type_^.base^.size;
  If y.mode<>mcReg Then Load(y);
  If s = 4 Then Put1(opLSL,y.r,y.r,2)
           Else Put1(Mul, y.r, y.r, s);
  If x.mode=mcVar Then Begin
   If x.r > 0 Then Put0(opAdd, y.r, SP, y.r)
              Else Put0(opAdd, y.r, SB, y.r);
   x.mode := mcRegI;
    x.r := y.r;
  End
   Else
  If x.mode=mcPar Then Begin
   Put2(Ldw, RH, SP, x.a);
   Put0(opAdd, y.r, RH, y.r);
   x.mode := mcRegI;
   x.r := y.r;
  End
   Else
  If x.mode=mcRegI Then Begin
   Put0(opAdd, x.r, x.r, y.r);
   Dec(RH);
  End;
 End;
End;

Procedure Not_(Var x:Item);
Var
 t:LongInt;
Begin
 If x.mode<>mcCond Then LoadCond(x);
 x.r:=Negated(x.r);
 t:=x.a;
 x.a:=x.b;
 x.b:=t;
End;

Procedure And1(var x: Item);Begin
 If x.mode<>mcCond Then LoadCond(x);
 Put3(BC,Negated(x.r),x.a);
 x.a:=pc-1;
 FixLink(x.b);
 x.b:=0;
End;

Procedure And2(Var x,y:Item);Begin
 If y.mode<>mcCond Then LoadCond(y);
 x.a:=merged(y.a, x.a);
 x.b:=y.b;
 x.r:=y.r;
End;

Procedure Or1(Var x:Item);Begin
 If x.mode<>mcCond Then LoadCond(x);
 Put3(BC, x.r, x.b);
 x.b:=pc-1;
 FixLink(x.a);
 x.a:=0;
End;

Procedure Or2(Var x,y:Item);Begin
 If y.mode<>mcCond Then LoadCond(y);
 x.a:=y.a;
 x.b:=merged(y.b, x.b);
 x.r:=y.r;
End;

Procedure Neg(Var x:Item);Begin
 If x.mode=mcConst Then x.a:=-x.a
  Else
 Begin
  Load(x);
  Put1(opMov,RH, 0, 0);
  Put0(opSUB,x.r, RH, x.r);
 End;
End;

Procedure AddOp(op:LongInt;Var x,y:Item);Begin
 If op=OSS._PLUS Then Begin
  If(x.mode=mcConst)and(y.mode=mcConst)Then x.a:=x.a+y.a Else
  If y.mode=mcConst Then Begin
   Load(x);
   If y.a <> 0 Then Put1(opAdd,x.r,x.r,y.a);
  End
   Else
  Begin
   Load(x);
   Load(y);
   Put0(opAdd,RH-2,x.r,y.r);
   Dec(RH);
   x.r := RH - 1;
  End;
 End
  Else
 Begin
  If(x.mode=mcConst)and(y.mode=mcConst)Then x.a:=x.a-y.a Else
  If y.mode=mcConst Then Begin
   Load(x);
   If y.a<>0 Then Put1(opSUB, x.r, x.r, y.a);
  End
   Else
  Begin
   load(x);
   load(y);
   Put0(opSUB,RH-2,x.r,y.r);
   Dec(RH);
   x.r:=RH-1;
  End;
 End;
End;

Procedure MulOp(Var x,y:Item);Begin
 If(x.mode=mcConst)and(y.mode=mcConst)Then x.a:=x.a*y.a Else
 If(y.mode=mcConst)and(y.a=2)Then Begin
  load(x);
  Put1(opLSL,x.r,x.r,1);
 End
  Else
 If y.mode=mcConst Then Begin
  Load(x);
  Put1(Mul, x.r, x.r, y.a);
 End
  Else
 If x.mode=mcConst Then Begin
  Load(y);
  Put1(Mul, y.r, y.r, x.a);
  x.mode:=mcReg;
  x.r:=y.r;
 End
  Else
 Begin
  load(x);
  load(y);
  Put0(Mul,RH-2,x.r,y.r);
  Dec(RH);
  x.r:=RH-1;
 End;
End;

Procedure DivOp(Op:Longint;Var x,y:Item);Begin
 If Op=OSS._DIV Then Begin
  If(x.mode=mcConst)and(y.mode=mcConst)Then Begin
   If y.a>0 Then x.a:=x.a div y.a
            Else OSS.Mark('Mauvais diviseur');
  End
   Else
  If(y.mode=mcConst)and(y.a=2)Then Begin
   Load(x);
   Put1(opASR, x.r, x.r, 1);
  End
   Else
  If y.mode=mcConst Then Begin
   If y.a>0 Then Begin
    Load(x);
    Put1(opDiv,x.r,x.r,y.a);
   End
    Else
   OSS.Mark('Mauvais diviseur');
  End
   Else
  Begin
   Load(y);
   Load(x);
   Put0(opDiv,RH-2,x.r,y.r);
   Dec(RH);
   x.r:=RH-1;
  End;
 End
  Else
 Begin
  If(x.mode=mcConst)and(y.mode=mcConst)Then Begin
   If y.a>0 Then x.a:=x.a mod y.a
            Else OSS.Mark('Mauvais restant');
  End
   Else
  If(y.mode=mcConst)and(y.a=2)Then Begin
   Load(x);
   Put1(opAnd,x.r,x.r,1);
  End
   Else
  If y.mode=mcConst Then Begin
   If y.a>0 Then Begin
    Load(x);
    Put1(opDiv,x.r,x.r,y.a);
    Put0(opMov+U,x.r,0,0);
   End
    Else
   OSS.Mark('Mauvais restant');
  End
   Else
  Begin
   Load(y);
   Load(x);
   Put0(opDiv,RH-2,x.r,y.r);
   Put0(opMov+U,RH-2,0,0);
   Dec(RH);
   x.r:=RH-1;
  End;
 End;
End;

Procedure Relation(op:Integer;Var x,y:Item);Begin
 If y.mode=mcConst Then Begin
  Load(x);
  Put1(opCMP,x.r,x.r,y.a);
  Dec(RH);
 End
  Else
 Begin
  load(x);
  load(y);
  Put0(opCMP,x.r,x.r,y.r);
  Dec(RH,2);
 End;
 SetCC(x,relmap[op-OSS._EQUAL]);
End;

Procedure Store(Var x,y:Item);Begin
 Load(y);
 If x.mode=mcVar Then Begin
  If x.r>0 Then Put2(Stw,y.r,SP,x.a)
           Else Put2(Stw,y.r,SB,x.a);
 End
  Else
 If x.mode=mcPar Then Begin
  Put2(Ldw, RH, SP, x.a);
  Put2(Stw, y.r, RH, x.b);
 End
  Else
 If x.mode = mcRegI Then Begin
  Put2(Stw, y.r, x.r, x.a);
  Dec(RH);
 End
  Else
 OSS.Mark('Association illÇgale');
 Dec(RH);
End;

Procedure VarParam(Var x:Item;ftype:TypePtr);
Var
 xmd:ModeClassType;
Begin
 xmd:=x.mode;
 LoadAdr(x);
 If(ftype^.DataType=ArrayDataType)and(ftype^.Len<0)Then Begin
  If x.type_^.len >= 0 Then Put1(opMov, RH, 0, x.type_^.len)
                       Else Put2(Ldw, RH, SP, x.a + 4);
  Inc(RH);
 End
  Else
 If ftype^.DataType=RecordDataType Then Begin
  If xmd = mcPar Then Put2(Ldw, RH, SP, x.a + 4);
  Inc(RH);
 End;
End;

Procedure ValueParam(Var x:Item);Begin
 Load(x);
End;

Procedure OpenArrayParam(Var x:Item);Begin
 LoadAdr(x);
 If x.Type_^.len>=0Then Begin
  Put1(opMov,RH,0,x.type_^.len)
 End
  Else
 Begin
  Put2(Ldw,RH,SP,x.a+4);
 End;
 Inc(RH);
End;

Procedure CFJump(Var x:Item);Begin  (*saut conditionnel en avant*)
 If x.mode<>mcCond Then Begin
  LoadCond(x);
 End;
 Put3(2,Negated(x.r),x.a);
 FixLink(x.b);
 x.a:=PC-1;
END;

Procedure FJump(Var L:LongInt);Begin (*saut inconditionnel en avant*)
 Put3(2, 7, L);
 L:=PC-1;
End;

Procedure CBJump(Var x:Item;L:LongInt);Begin (*saut conditionnel en arriäre*)
 If x.Mode<>mcCond Then Begin
  loadCond(x);
 End;
 Put3(2,Negated(x.r),L-PC-1);
End;

Procedure BJump(L:LongInt);Begin (*saut inconditionnel en arriäre*)
 Put3(2,7,L-PC-1);
End;

Procedure Call(Var Obj:ObjectPtr);Begin
 Put3(3, 7, obj^.val - pc - 1);
 RH := 0;
End;

Procedure Enter(ParBlkSize,LocBlkSize:LongInt);
Var
 a,r:LongInt;
Begin
 a:=4;
 r:=0;
 Put1(opSUB,SP,SP,LocBlkSize);
 Put2(Stw,LNK,SP,0);
 While a<ParBlkSize do Begin
  Put2(Stw,r,SP,a);
  Inc(r);
  Inc(a, 4);
 End;
End;

Procedure Return(size:LongInt);Begin
 Put2(Ldw,LNK,SP,0);
 Put1(opAdd,SP,SP,Size);
 Put3(BR,7,LNK);
 RH:=0;
End;

Procedure Ord(Var x:Item);Begin
 Load(x);
 x.type_:=intType;
End;

Procedure ReadInt(Var x:Item);Begin
 LoadAdr(x);
 Put1(opMov,RH,0,-4);
 Put2(Ldw,RH,RH,0);
 Put2(Stw,RH,x.r,0);
 Dec(RH);
End;

Procedure eot(Var x:Item);Begin
 Put1(opMov,RH,0,-8);
 Put2(Ldw,RH,RH,0);
 SetCC(x,EQ);
End;

Procedure WriteInt(Var x:Item);Begin
 Load(x);
 Put1(opMov,RH,0,-4);
 Put2(Stw,x.r,RH,0);
 Dec(RH);
End;

Procedure WriteChar(Var x:Item);Begin
 Load(x);
 Put1(opMov,RH, 0, -8);
 Put2(Stw, x.r, RH, 0);
 Dec(RH);
End;

Procedure WriteLine;Begin
 Put1(opMov,RH,0,-12);
 Put2(Stw,RH,RH,0);
End;

Procedure Open;Begin
 CurLev:=0;
 PC:=0;
 RH:=0;
 Put3(2,7,0);
End;

Procedure Header(size:LongInt);Begin
 Entry:=PC;
 Fix(0,PC-1);
End;

Procedure Close;Begin
 Put1(opMov,0,0,0);
 Put3(0,7,0);
End;

Procedure WriteReg(R:LongInt);Begin
 Write(' ');
 If r<13 Then Write('R',R) Else
 If r=13 Then Write('SB') Else
 If r=14 Then Write('SP') Else
 If r=15 Then Write('LNK');
End;

Procedure WriteHex(X:LongInt);Begin
 Write(LongHex2Str(X));
End;

Procedure Decode;
Var
 i,w,a,b,c,op:LongInt;
Begin
 i:=0;
 WriteLn('Addr Opcode    Assembleur');
 WriteLn('---- --------- ----------');
 While i<PC do Begin
  w:=code[i];
  a:=w div $1000000 mod $10;
  b:=w div $100000 mod $10;
  Write(i:4,' ');
  WriteHex(w);
  Write(': ');
  If not (w div $80000000) AND 1<>0 Then Begin
   op:=w div $10000 MOD $10;
   Write(mnemo0[op]);
   WriteReg(a);
   WriteReg(b);
   If Not(w div $40000000) and 1 <> 0 Then Begin
    WriteReg(w MOD $10);
   End
    Else
   Begin
    c:=w mod $10000;
    If(w div $10000000)and 1<>0 Then Begin
     c:=c+LongInt($FFFF0000);
    End;
    Write(c, 8);
   End;
  End
   Else
  If not (w div $40000000) and 1<>0 Then Begin
   If(w div $20000000)and 1<>0 Then Write('STW ')
                               Else Write('LDW');
   WriteReg(a);
   WriteReg(b);
   Write(w MOD $100000, 8);
  End
   Else
  Begin
   Write('B');
   If(w div $10000000)and 1<>0 Then Begin
    Write('L');
   End;
   Write(mnemo1[a]);
   If Not(w div $20000000) and 1<>0 Then Begin
    WriteReg(w MOD $10);
   End
    Else
   Begin
    w:=w mod $1000000;
    If w>=$800000 Then Begin
     w:=w-$1000000;
    End;
    Write(w, 8);
   End;
  End;
  WriteLn;
  Inc(i);
 End;
 WriteLn;
End;

Function HexCh(k:LongInt):Char;Begin
 If k >= 10 Then Begin
  Inc(k,$27);
 End;
 HexCh:=Chr(k+$30);
END;

Procedure Execute;Begin
 RISC.Execute(Code,{MemSize}PC,PC);
End;

BEGIN
 New(boolType);
 If(BoolType=NIL)Then Begin
  WriteLn('Manque de mÇmoire');
  Halt;
 End;
 boolType^.DataType:=BooleanDataType;
 boolType^.Size:=4;
 New(intType);
 If(intType=NIL)Then Begin
  WriteLn('Manque de mÇmoire');
  Halt;
 End;
 intType^.DataType:=IntegerDataType;
 intType^.Size:=4;
 relmap[0]:=EQ;
 relmap[1]:=NE;
 relmap[2]:=LT;
 relmap[3]:=LE;
 relmap[4]:=GT;
 relmap[5]:=GE;
 mnemo0[opMov]:='MOV';
 mnemo0[opLsl]:='LSL';
 mnemo0[opAsr]:='ASR';
 mnemo0[opRor]:='ROR';
 mnemo0[opAnd]:='AND';
 mnemo0[opAnn]:='ANN';
 mnemo0[opIor]:='IOR';
 mnemo0[opXor]:='XOR';
 mnemo0[opAdd]:='ADD';
 mnemo0[opSub]:='SUB';
 mnemo0[opMul]:='MUL';
 mnemo0[opDiv]:='DIV';
 mnemo1[PL]:='PL ';
 mnemo1[MI]:='MI ';
 mnemo1[EQ]:='EQ ';
 mnemo1[NE]:='NE ';
 mnemo1[LT]:='LT ';
 mnemo1[GE]:='GE ';
 mnemo1[LE]:='LE ';
 mnemo1[GT]:='GT ';
 mnemo1[15]:='NO ';
END.