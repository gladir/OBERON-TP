{ @author: Sylvain Maltais (support@gladir.com)
  @source: Bas‚ sur le livre "Compiler Construction" de Niklaus Wirth's
  @created: 2023
  @website(https://www.gladir.com/CODER/OBERON-TP)
  @abstract(Target: Turbo Pascal 7, Free Pascal 3.2)
}

Program OSP;

Uses Crt,DOS,Strings,OSG,OSS;

Const
 WordSize=4;

Var
 CompileOutput:(oMemory,oDisk);
 FlagDecode:Boolean;
 FileOutput:File;
 ByteWrited:Word;
 I:Integer;
 Path:String;
 Sym,Level:Integer;
 topScope,universe,Dummy:ObjectPtr;
 Expression1:Procedure(Var x:OSG.Item);

Function StrToUpper(S:String):String;
Var
 I:Byte;
Begin
 For I:=1 to Length(S)do Begin
  If S[I] in['a'..'z']Then S[I]:=Chr(System.Ord(S[I])-32);
 End;
 StrToUpper:=S;
End;

Function Path2NoExt(S:String):String;
Var
 D:DirStr;
 N:NameStr;
 E:ExtStr;
Begin
 FSplit(S,D,N,E);
 Path2NoExt:=D+N;
End;


Procedure NewObj(Var obj:ObjectPtr;IClass:ModeClassType);
Var
 NewPtr,x:ObjectPtr;
Begin
 x:=topScope;
 While(x^.next<>NIL)and({StrComp(x^.next^.name,OSS.id)<>0}x^.next^.name <> OSS.id) do Begin
  x:=x^.next;
 End;
 If x^.next=NIL Then Begin
  New(NewPtr);
  If(NewPtr=NIL)Then Begin
   WriteLn('Manque de m‚moire');
   Halt;
  End;
  NewPtr^.name:=OSS.id;
  NewPtr^.class_:=IClass;
  NewPtr^.next:=NIL;
  x^.next:=NewPtr;
  obj:=NewPtr;
 End
  Else
 Begin
  obj:=x^.next;
  OSS.Mark('mult def');
 End;
End;

Procedure Find(Var Obj:ObjectPtr);
Var
 s,x:ObjectPtr;
Begin
 s:=topScope;
 Repeat
  x:=s^.next;
  While(x<>NIL)and({StrComp(x^.Name,OSS.id)<>0}x^.Name<>OSS.id)do Begin
   x:=x^.next;
  End;
  s:=s^.dsc;
 Until(x<>NIL)or(s=NIL);
 If x=NIL Then Begin
  x:=Dummy;
  OSS.Mark('undef');
 End;
 Obj:=x;
End;

Procedure FindField(Var Obj:ObjectPtr;List:ObjectPtr);Begin
 While(List<>NIL)and({StrComp(List^.Name,OSS.id)<>0}List^.Name<>OSS.id) do Begin
  List:=List^.Next;
 End;
 If List<>NIL Then Begin
  obj:=List;
 End
  Else
 Begin
  OSS.Mark('undef');
  obj:=Dummy;
 End;
End;

Procedure Check(S:Integer;Msg:String);Begin
 If Sym=S Then Begin
  OSS.Get(sym);
 End
  Else
 Begin
  OSS.Mark(msg);
 End;
End;

Procedure CheckInt(Var x:OSG.Item);Begin
 If x.type_^.DataType<>OSG.IntegerDataType Then Begin
  OSS.Mark('not integer');
 End;
End;

Procedure CheckBool(Var x:OSG.Item);Begin
 If x.type_^.DataType<>OSG.BooleanDataType Then Begin
  OSS.Mark('not Boolean');
 End;
End;

Procedure OpenScope;
Var
 S:ObjectPtr;
Begin
 New(s);
 If(s=NIL)Then Begin
  WriteLn('Manque de m‚moire');
  Halt;
 End;
 s^.class_:=OSG.mcHead;
 s^.dsc:=topScope;
 s^.next:=NIL;
 topScope:=s;
End;

Procedure CloseScope;Begin
 topScope:=topScope^.dsc;
End;

Procedure Selector(Var x:OSG.Item);
Var
 y:OSG.Item;
 obj:ObjectPtr;
Begin
 While(Sym=OSS._LBRAKET)or(Sym=OSS._PERIOD)do Begin
  If Sym=OSS._LBRAKET Then Begin
   OSS.Get(sym);
   Expression1(y);
   If x.type_^.DataType=OSG.ArrayDataType Then Begin
    CheckInt(y);
    OSG.Index(x, y);
    x.Type_:=x.type_^.base;
   End
    Else
   Begin
    OSS.Mark('Ce n''est pas un tableau');
   End;
   Check(OSS._RBRAKET, 'Pas de ]');
  End
   Else (* Point *)
  Begin
   OSS.Get(sym);
   If Sym=OSS._IDENT Then Begin
    If x.type_^.DataType=OSG.RecordDataType Then Begin
     FindField(obj,x.type_^.dsc);
     OSS.Get(sym);
     If obj<>NIL Then Begin
      OSG.Field(x,Obj);
      x.type_:=Obj^.PType;
     End;
    End
     Else
    Begin
     OSS.Mark('Ce n''est pas un enregistrement');
    End;
   End
    Else
   Begin
    OSS.Mark('ident?');
   End;
  End;
 End;
END;

Function CompTypes(t0,t1:OSG.TypePtr):Boolean;Begin
 CompTypes:=(t0=t1)or
         ((t0^.DataType=OSG.ArrayDataType)and(t1^.DataType=OSG.ArrayDataType)and CompTypes(t0^.base,t1^.base));
End;

Procedure Parameter(Par:OSG.ObjectPtr);
Var
 x:OSG.Item;
 VarPar:Boolean;
Begin
 Expression1(x);
 If Par<>NIL Then Begin
  VarPar:=Par^.class_=OSG.mcPar;
  If CompTypes(Par^.PType,X.type_)Then Begin
   If NOT varpar Then Begin
    OSG.ValueParam(x);
   End
    Else
   Begin
    OSG.VarParam(x, par^.PType);
   End;
  End
   Else
  If(x.type_^.DataType=OSG.ArrayDataType)and
    (par^.PType^.DataType=OSG.ArrayDataType)and
    (x.type_^.base^.DataType=par^.PType^.base^.DataType)and
    (par^.PType^.len<0)Then Begin
   OSG.OpenArrayParam(x);
  End
   Else
  Begin
   OSS.Mark('ParamŠtres incompatible');
  End;
 End;
End;

Procedure ParamList(Var obj:ObjectPtr);
Var
 n:Integer;
 par:ObjectPtr;
Begin
 Par:=obj^.dsc;
 n:=0;
 If Sym<>OSS._RPARENT Then Begin
  Parameter(par);
  Inc(n);
  While Sym<=OSS._COMMA do Begin
   Check(sym, 'Virgule?');
   If par <> NIL Then Begin
    Par:=Par^.Next;
   End;
   Inc(n);
   Parameter(par);
  End;
  Check(OSS._RPARENT,') attendue');
 End
  Else
 Begin
  OSS.Get(sym);
 End;
 If n<obj^.nofpar Then Begin
  OSS.Mark('Pas assez de paramŠtres');
 End
  Else
 If n>Obj^.nofpar Then Begin
  OSS.Mark('Trop de paramŠtres');
 End;
End;

Procedure StandFunc(Var x:OSG.Item;fctno:LongInt);Begin
 If Sym=OSS._LPAREN Then Begin
  OSS.Get(sym);
  If fctno = 0 Then Begin (*ORD*)
   Expression1(x);
   OSG.Ord(x);
  End
   Else
  If fctno = 1 Then Begin (*eot*)
   OSG.eot(x);
  End;
  If Sym=OSS._RPARENT Then Begin
   OSS.Get(sym);
  End
   Else
  Begin
   OSS.Mark('ParenthŠse de droite attendue');
  End;
 End
  Else
 Begin
  OSS.Mark('ParamŠtre attendue');
  OSG.MakeConstItem(x, OSG.intType, 0);
 End;
End;

Procedure Factor(Var x:OSG.Item);
Var
 obj:OSG.ObjectPtr;
Begin
 If(Sym<OSS._CHAR)or(Sym>OSS._IDENT)Then Begin
  OSS.Mark('Expression attendue');
  Repeat
   OSS.Get(sym);
  Until(Sym>=OSS._INT)and(Sym<=OSS._IDENT);
 End;
 If Sym=OSS._IDENT Then Begin
  Find(obj);
  OSS.Get(sym);
  If Obj^.Class_=OSG.mcSFunc Then Begin
   If Obj^.Ptype=NIL Then Begin
    OSS.Mark('Ce n''est pas une fonction');
    obj^.PType := OSG.intType;
   End;
   StandFunc(x, obj^.val);
   x.type_ := obj^.PType;
  End
   Else
  Begin
   OSG.MakeItem(x,obj,level);
   Selector(x);
  End;
 End
  Else
 If Sym=OSS._INT Then Begin
  OSG.MakeConstItem(x, OSG.intType, OSS.val);
  OSS.Get(sym);
 End
  Else
 If Sym=OSS._CHAR Then Begin
  OSG.MakeConstItem(x, OSG.intType, OSS.val);
  OSS.Get(sym);
 End
  Else
 If Sym=OSS._LPAREN Then Begin
  OSS.Get(sym);
  If Sym<>OSS._RPARENT Then Begin
   Expression1(x);
  End;
  Check(OSS._RPARENT, 'Pas de )');
 End
  Else
 If Sym=OSS._NOT Then Begin
  OSS.Get(sym);
  Factor(x);
  CheckBool(x);
  OSG.Not_(x);
 End
  Else
 If Sym=OSS._FALSE Then Begin
  OSS.Get(sym);
  OSG.MakeConstItem(x, OSG.boolType, 0);
 End
  Else
 If Sym=OSS._TRUE Then Begin
  OSS.Get(sym);
  OSG.MakeConstItem(x, OSG.boolType, 1);
 End
  Else
 Begin
  OSS.Mark('Facteur ?');
  OSG.MakeItem(x, dummy, level);
 End;
End;

Procedure Term(Var x:OSG.Item);
Var
 y:OSG.Item;
 op:Integer;
Begin
 Factor(x);
 While(Sym>=OSS._TIMES)and(Sym<=OSS._AND)do Begin
  op:=Sym;
  OSS.Get(sym);
  If(Op=OSS._TIMES)Then Begin
   CheckInt(x);
   Factor(y);
   CheckInt(y);
   OSG.MulOp(x, y);
  End
   Else
  If(Op=OSS._DIV)or(Op=OSS._MOD)Then Begin
   CheckInt(x);
   factor(y);
   CheckInt(y);
   OSG.DivOp(op, x, y);
  End
   Else
  Begin (*op = and*)
   CheckBool(x);
   OSG.And1(x);
   factor(y);
   CheckBool(y);
   OSG.And2(x, y);
  End;
 End;
End;

Procedure SimpleExpression(Var X:OSG.Item);
Var
 y:OSG.Item;
 op:Integer;
Begin
 If Sym=OSS._PLUS Then Begin
  OSS.Get(sym);
  Term(x);
  CheckInt(x);
 End
  Else
 If Sym=OSS._MINUS Then Begin
  OSS.Get(sym);
  Term(x);
  CheckInt(x);
  OSG.Neg(x);
 End
  Else
 Begin
  Term(x);
 End;
 While(Sym>=OSS._PLUS)and(Sym<=OSS._OR) do Begin
  Op:=Sym;
  OSS.Get(sym);
  If Op=OSS._OR Then Begin
   OSG.Or1(x);
   CheckBool(x);
   Term(y);
   CheckBool(y);
   OSG.Or2(x,y);
  End
   Else
  Begin
   CheckInt(x);
   Term(y);
   CheckInt(y);
   OSG.AddOp(op, x, y);
  End;
 End;
End;

Procedure Expression(Var x:OSG.Item);Far;
Var
 y:OSG.Item;
 op:Integer;
Begin
 SimpleExpression(x);
 If(Sym>=OSS._EQUAL)and(Sym<=OSS._GEQ)Then Begin
  Op:=Sym;
  OSS.Get(sym);
  SimpleExpression(y);
  If(X.Type_=Y.Type_)THEN Begin
   OSG.Relation(op, x, y);
  End
   Else
  Begin
   OSS.Mark('Les types sont incompatibles');
  End;
  x.type_:=OSG.boolType;
 End;
End;

Procedure StandProc(PNo:LongInt);
Var
 X:OSG.Item;
Begin
 If Sym=OSS._LPAREN Then Begin
  OSS.Get(sym);
  Expression(x);
  If PNo=0 Then Begin
   OSG.ReadInt(x);
  End
   Else
  If PNo=1 Then Begin
   OSG.WriteInt(x);
  End
   Else
  If PNo=2 Then Begin
   OSG.WriteChar(x)
  End
   Else
  Begin
   OSS.Mark('Pas de parenthŠse de gauche');
  End;
  If Sym=OSS._RPARENT Then Begin
   OSS.Get(sym);
  End
   Else
  Begin
   OSS.Mark('Pas de parenthŠse de droite');
  End;
 End
  Else
 If PNo=3 Then Begin
  OSG.WriteLine;
 End;
End;

Procedure StatSequence;
Var
 obj:ObjectPtr;
 x,y:OSG.Item;
 L:LongInt;
Begin
 Repeat
  { sync }
  obj:=NIL;
  If Not((Sym=OSS._IDENT)or((Sym>=OSS._IF)and(Sym<=OSS._REPEAT))or
         (Sym>=OSS._SEMICOLON))Then Begin
   OSS.Mark('Instruction attendue');
   Repeat
    OSS.Get(sym);
   Until(Sym=OSS._IDENT)or(Sym>=OSS._IF);
  End;
  If Sym=OSS._IDENT Then Begin
   Find(Obj);
   OSS.Get(sym);
   If Obj^.class_=OSG.mcSProc Then StandProc(obj^.val)
    Else
   Begin
    OSG.MakeItem(X,Obj,Level);
    Selector(X);
    If Sym=OSS._BECOMES Then Begin { association }
     OSS.Get(sym);
     Expression(y);
     If(X.Type_^.DataType in[OSG.BooleanDataType,OSG.IntegerDataType])and
       (X.Type_^.DataType=Y.Type_^.DataType)Then Begin
            OSG.Store(x, y)
     End
      Else
     Begin
      OSS.Mark('Association incompatible');
     End;
    End
     Else
    If Sym=OSS._EQUAL Then Begin
     OSS.Mark('Doit ˆtre :=');
     OSS.Get(sym);
     Expression(y);
    End
     Else
    If Sym=OSS._LPAREN Then Begin { Appel de proc‚dure }
     OSS.Get(sym);
     If(Obj^.class_=OSG.mcProc)and(Obj^.PType=NIL)Then Begin
      ParamList(obj);
      OSG.Call(obj);
     End
      Else
     Begin
      OSS.Mark('Ce n''est pas une proc‚dure');
     End;
    End
     Else
    If Obj^.Class_=OSG.mcProc Then Begin { Appel de proc‚dure sans paramŠtres }
     If Obj^.Nofpar>0 Then Begin
      OSS.Mark('ParamŠtres attendue');
     End;
     If Obj^.PType=NIL Then Begin
      OSG.Call(obj);
     End
      Else
     Begin
      OSS.Mark('Ce n''est pas une proc‚dure');
     End;
    End
     Else
    If(Obj^.class_=OSG.mcSProc)and(Obj^.val=3)Then Begin
     OSG.WriteLine;
    End
     Else
    If Obj^.Class_=OSG.mcTyp Then Begin
     OSS.Mark('Association ill‚gale');
    End
     Else
    Begin
     OSS.Mark('Ce n''est pas une proc‚dure');
    End;
   End;
  End
   Else
  If Sym=OSS._IF Then Begin
   OSS.Get(sym);
   Expression(x);
   CheckBool(x);
   OSG.CFJump(x);
   Check(OSS._THEN, 'Pas de THEN');
   StatSequence;
   L:=0;
   While Sym=OSS._ELSIF do Begin
    OSS.Get(sym);
    OSG.FJump(L);
    OSG.FixLink(x.a);
    Expression(x);
    CheckBool(x);
    OSG.CFJump(x);
    If Sym=OSS._THEN Then Begin
     OSS.Get(sym);
    End
     Else
    Begin
     OSS.Mark('THEN?');
    End;
    StatSequence;
   End;
   If Sym=OSS._ELSE Then Begin
    OSS.Get(sym);
    OSG.FJump(L);
    OSG.FixLink(x.a);
    StatSequence;
   End
    Else
   Begin
    OSG.FixLink(x.a);
   End;
   OSG.FixLink(L);
   If Sym=OSS._END Then Begin
    OSS.Get(sym);
   End
    Else
   Begin
    OSS.Mark('END?');
   End;
  End
   Else
  If Sym=OSS._WHILE Then Begin
   OSS.Get(sym);
   L:=OSG.PC;
   Expression(x);
   CheckBool(x);
   OSG.CFJump(x);
   Check(OSS._DO,'Pas de DO');
   StatSequence;
   OSG.BJump(L);
   OSG.FixLink(x.a);
   Check(OSS._END, 'Pas de END');
  End
   Else
  If Sym=OSS._REPEAT Then Begin
   OSS.Get(sym);
   L:=OSG.pc;
   StatSequence;
   If Sym=OSS._UNTIL Then Begin
    OSS.Get(sym);
    Expression(x);
    CheckBool(x);
    OSG.CBJump(x, L);
   End
    Else
   Begin
    OSS.Mark('UNTIL attendue');
    OSS.Get(sym);
   End;
  End;
  OSG.CheckRegs;
  If Sym=OSS._SEMICOLON Then Begin
   OSS.Get(sym)
  End
   Else
  If Sym<OSS._SEMICOLON THEN Begin
   OSS.Mark('Point-virgule attendue?');
  End;
 Until Sym>OSS._SEMICOLON;
End;

Procedure IdentList(Class:ModeClassType;Var First:ObjectPtr);
Var
 Obj:ObjectPtr;
Begin
 If Sym=OSS._IDENT Then Begin
  NewObj(first,Class);
  OSS.Get(sym);
  While Sym=OSS._COMMA do Begin
   OSS.Get(sym);
   If Sym=OSS._IDENT Then Begin
    NewObj(obj,class);
    OSS.Get(sym);
   End
    Else
   Begin
    OSS.Mark('ident?');
   End;
  End;
  Check(OSS._COLON, 'no :');
 End;
End;

Procedure A_Type(Var type_:OSG.TypePtr);
Var
 Obj,First:ObjectPtr;
 X:OSG.Item;
 TP:OSG.TypePtr;
Begin
 Type_:=OSG.intType;
 If(Sym<>OSS._IDENT)and(Sym<OSS._ARRAY)Then Begin
  OSS.Mark('type?');
  Repeat
   OSS.Get(sym);
  Until(Sym=OSS._IDENT)or(Sym>=OSS._ARRAY);
 End;
 If Sym=OSS._IDENT Then Begin
  Find(obj);
  OSS.Get(sym);
  If Obj^.Class_=OSG.mcTyp Then Begin
   Type_:=Obj^.PType;
  End
   Else
  Begin
   OSS.Mark('type?');
  End;
 End
  Else
 If Sym=OSS._ARRAY Then Begin
  OSS.Get(sym);
  Expression(x);
  If(X.Mode<>OSG.mcConst)or(X.A<0)Then Begin
   OSS.Mark('Mauvaise index');
  End;
  If Sym=OSS._OF Then Begin
   OSS.Get(sym);
  End
   Else
  Begin
   OSS.Mark('OF?');
  End;
  A_Type(tp);
  New(type_);
   If(type_=NIL)Then Begin
   WriteLn('Manque de m‚moire');
   Halt;
  End;
  Type_^.DataType:=OSG.ArrayDataType;
  Type_^.base:=TP;
  Type_^.len:=x.a;
  If(TP<>NIL)Then Type_^.size:=Type_^.Len*TP^.Size
             Else Type_^.size:=Type_^.Len*0;
 End
  Else
 If Sym=OSS._RECORD Then Begin
  OSS.Get(sym);
  New(type_);
  If(type_=NIL)Then Begin
   WriteLn('Manque de m‚moire');
   Halt;
  End;
  Type_^.DataType:=OSG.RecordDataType;
  Type_^.Size:=0;
  OpenScope;
  Repeat
   If Sym=OSS._IDENT Then Begin
    IdentList(OSG.mcFld,First);
    A_Type(tp);
    Obj:=First;
    While obj <> NIL do Begin
     Obj^.PType:=TP;
     Obj^.Val:=Type_^.Size;
     Type_^.Size:=Type_^.Size+Obj^.PType^.size;
     Obj:=Obj^.next;
    End;
   End;
   If Sym=OSS._SEMICOLON Then Begin
    OSS.Get(sym);
   End
    Else
   If Sym=OSS._IDENT Then Begin
    OSS.Mark('; ?');
   End;
  Until Sym<>OSS._IDENT;
  Type_^.Dsc:=TopScope^.next;
  CloseScope;
  Check(OSS._END, 'Pas de END');
 End
  Else
 Begin
  OSS.Mark('Identificateur?');
 End;
End;

Procedure Declarations(Var VarSize:LongInt);
Var
 Obj,First:ObjectPtr;
 x:OSG.Item;
 tp:OSG.TypePtr;
Begin
 If(Sym<OSS._CONST)and(Sym<>OSS._END)Then Begin
  OSS.Mark('D‚claration?');
  Repeat
   OSS.Get(sym);
  Until(Sym>=OSS._CONST)or(Sym=OSS._END);
 End;
 If(Sym=OSS._CONST)Then Begin
  OSS.Get(sym);
  While Sym=OSS._IDENT do Begin
   NewObj(obj,OSG.mcConst);
   OSS.Get(sym);
   If(Sym=OSS._EQUAL)Then Begin
    OSS.Get(sym);
   End
    Else
   Begin
    OSS.Mark('=?');
   End;
   Expression(x);
   If(x.mode=OSG.mcConst)Then Begin
    Obj^.val:=x.a;
    Obj^.PType:=X.type_;
   End
    Else
   OSS.Mark('expression non constante');
   Check(OSS._SEMICOLON, '; attendue');
  End;
 End;
 If(Sym=OSS._TYPE)Then Begin
  OSS.Get(sym);
  While(Sym=OSS._IDENT)do Begin
   NewObj(obj,OSG.mcTyp);
   OSS.Get(sym);
   If(Sym=OSS._EQUAL)Then OSS.Get(sym)
                     Else OSS.Mark('=?');
   A_Type(obj^.PType);
   Check(OSS._SEMICOLON, '; attendue');
  End;
 End;
 If(Sym=OSS._VAR)Then Begin
  OSS.Get(sym);
  While(Sym=OSS._IDENT)do Begin
   IdentList(OSG.mcVar,First);
   A_Type(tp);
   Obj:=First;
   While(Obj<>NIL)do Begin
    obj^.PType:=tp;
    obj^.lev:=level;
    obj^.val:=varsize;
   If obj^.PType<>NIL Then varsize:=varsize+obj^.PType^.size;
    obj:=obj^.next;
   End;
   Check(OSS._SEMICOLON, '; attendue');
  End;
 End;
 If(Sym>=OSS._CONST)and(Sym<=OSS._VAR)Then Begin
  OSS.Mark('D‚claration en mauvais ‚tat');
 End;
End;

Procedure ProcedureDecl;
Const
 MarkSize = 4;
Var
 Proc:ObjectPtr;
 ProcId:OSS.Ident;
 NofPar:Integer;
 LocblkSize,ParBlkSize:LongInt;

 Procedure FPSection(Var Adr:LongInt;Var NofPar:Integer);
 Var
  Obj,First:ObjectPtr;
  TP:OSG.TypePtr;
  ParSize:LongInt;
 Begin
  If Sym=OSS._VAR Then Begin
   OSS.Get(sym);
   IdentList(OSG.mcPar,First)
  End
   Else
  Begin
   IdentList(OSG.mcVar,First);
  End;
  If Sym=OSS._IDENT Then Begin
   Find(obj);
   OSS.Get(sym);
   If Obj^.class_=OSG.mcTyp Then Begin
    TP:=Obj^.PType;
   End
    Else
   Begin
    OSS.Mark('Type?');
    TP:=OSG.intType;
   End;
  End
   Else
  Begin
   OSS.Mark('Identificateur?');
   TP:=OSG.intType;
  End;
  If First^.Class_=OSG.mcVar Then Begin
   ParSize:=TP^.Size;
   If TP^.DataType>=OSG.ArrayDataType Then Begin
    OSS.Mark('Pas de paramŠtres de structure');
   End;
  End
   Else
  Begin
   ParSize:=WordSize;
  End;
  Obj:=First;
  While Obj<>NIL do Begin
   Inc(nofpar);
   Obj^.PType:=TP;
   Obj^.Lev:=Level;
   Obj^.Val:=Adr;
   Adr:=Adr+ParSize;
   Obj:=Obj^.next;
  End;
 End;

Begin (* ProcedureDecl *)
 OSS.Get(sym);
 If Sym=OSS._IDENT Then Begin
  ProcId:=OSS.id;
  NewObj(Proc,OSG.mcProc);
  OSS.Get(sym);
  ParBlkSize:=MarkSize;
  NofPar:=0;
  OpenScope;
  Inc(Level);
  Proc^.val:=-1;
  If Sym=OSS._LPAREN Then Begin
   OSS.Get(sym);
   If Sym=OSS._RPARENT Then Begin
    OSS.Get(sym)
   End
    Else
   Begin
    FPSection(ParBlkSize,NofPar);
    While Sym=OSS._SEMICOLON do Begin
     OSS.Get(sym);
     FPSection(ParBlkSize,NofPar);
    End;
    If Sym=OSS._RPARENT Then Begin
     OSS.Get(sym)
    End
     Else
    Begin
     OSS.Mark(')?');
    End;
   End;
  End;
  LocBlkSize:=ParBlkSize;
  Proc^.PType:=NIL;
  Proc^.dsc:=TopScope^.next;
  Proc^.nofpar:=NofPar;
  Check(OSS._SEMICOLON, '; attendue');
  Declarations(locblksize);
  Proc^.dsc:=TopScope^.next;
  While Sym=OSS._PROCEDURE do Begin
   ProcedureDecl;
   Check(OSS._SEMICOLON, '; attendue');
  End;
  Proc^.val := OSG.pc;
  OSG.Enter(parblksize, locblksize);
  If Sym=OSS._BEGIN Then Begin
   OSS.Get(sym);
   StatSequence;
  End;
  Check(OSS._END, 'Pas de END');
  If Sym=OSS._IDENT Then Begin
   If procid <> OSS.id Then Begin
    OSS.Mark('no match');
   End;
   OSS.Get(sym);
  End;
  OSG.Return(locblksize);
  Dec(level);
  CloseScope;
 End;
End;

Procedure Module;
Var
 modid:OSS.Ident;
 dc,tag:LongInt;
Begin
 Write('  compilation ');
 If sym=OSS._MODULE Then Begin
  OSS.Get(sym);
  If Sym=OSS._TIMES Then Begin
   Tag:=1;
   OSS.Get(sym);
  End
   Else
  Begin
   Tag:=0;
  End;
  OSG.Open;
  OpenScope;
  dc:=0;
  Level:=0;
  If sym=OSS._IDENT Then Begin
   modid := OSS.id;
   OSS.Get(sym);
   System.WriteLn(modid);
  End
   Else
  Begin
   OSS.Mark('ident?');
  End;
  Check(OSS._SEMICOLON, '; attendue');
  Declarations(dc);
  While sym=OSS._PROCEDURE do Begin
   ProcedureDecl;
   Check(OSS._SEMICOLON, '; attendue');
  End;
  OSG.Header(dc);
  If sym = OSS._BEGIN Then Begin
   OSS.Get(sym);
   StatSequence;
  End;
  Check(OSS._END,'Pas de END');
  If sym=OSS._IDENT Then Begin
   If modid<>OSS.id Then Begin
    OSS.Mark('Pas de correspondance');
   End;
   OSS.Get(sym);
  End
   Else
  Begin
   OSS.Mark('ident?');
  End;
  If sym<>OSS._PERIOD Then Begin
   OSS.Mark('. ?');
  End;
  CloseScope;
  If Not OSS.error Then Begin
   OSG.Close;
   Write('code g‚n‚r‚');
   Write(OSG.pc:6);
   Write(dc:6);
   System.WriteLn;
  End;
 End
  Else
 Begin
  OSS.Mark('MODULE?');
 End;
End;

Procedure Enter(Name:String;cl:ModeClassType;n:LongInt;type_:OSG.TypePtr);
Var
 obj:ObjectPtr;
Begin
 New(obj);
 If(obj=NIL)Then Begin
  WriteLn('Manque de m‚moire');
  Halt;
 End;
 obj^.class_:=cl;
 obj^.val:=n;
 StrPCopy(obj^.name,Name);
 obj^.PType:=type_;
 obj^.dsc:=NIL;
 obj^.next:=topScope^.next;
 topScope^.next:=obj;
End;

BEGIN
 {$IFDEF FPC}
  {$IFDEF WINDOWS}
   SetUseACP(False);
  {$ENDIF}
 {$ENDIF}
 If(ParamStr(1)='/?')or(ParamStr(1)='--help')or(ParamStr(1)='-h')or
   (ParamStr(1)='/h')or(ParamStr(1)='/H')Then Begin
  WriteLn('OBERON : Cette commande permet de lancer le compilateur de ',
                   'langage de programmation OBERON.');
  WriteLn;
  WriteLn('Syntaxe : OBERON fichier.MOD [/OUTPUT:DISK]');
  WriteLn;
  WriteLn('fichier      Ce paramŠtre permet d''indiquer un fichier de code source');
  WriteLn('/DECODE      Ce paramŠtre permet d''afficher le code assembleur g‚n‚r‚');
  WriteLn('/OUTPUT:DISK Ce paramŠtre permet d''indiquer ',
                       'd''‚crire le fichier sur disque');
 End
  Else
 If ParamCount>0Then Begin
  CompileOutput:=oMemory;
  FlagDecode:=False;
  Sym:=0;
  Level:=0;
  New(dummy);
  If(dummy=NIL)Then Begin
   WriteLn('Manque de m‚moire');
   Halt;
  End;
  dummy^.class_:=OSG.mcVar;
  dummy^.PType:=OSG.intType;
  dummy^.val:=0;
  topScope:=NIL;
  OpenScope;
  {$IFDEF FPC}
   Expression1:=@Expression;
  {$ELSE}
   Expression1:=Expression;
  {$ENDIF}
  Enter('eot', OSG.mcSFunc, 1, OSG.boolType);
  Enter('ReadInt', OSG.mcSProc, 0, NIL);
  Enter('WriteInt', OSG.mcSProc, 1, NIL);
  Enter('WriteChar ', OSG.mcSProc, 2, NIL);
  Enter('WriteLn', OSG.mcSProc, 3, NIL);
  Enter('ORD', OSG.mcSFunc, 0, OSG.intType);
  Enter('BOOLEAN', OSG.mcTyp, 0, OSG.boolType);
  Enter('INTEGER', OSG.mcTyp, 1, OSG.intType);
  Universe:=topScope;
  For I:=1 to ParamCount do Begin
   If StrToUpper(ParamStr(I))='/DECODE'Then FlagDecode:=True Else
   If Copy(StrToUpper(ParamStr(I)),1,8)='/OUTPUT:'Then Begin
    If Copy(StrToUpper(ParamStr(I)),9,255)='FILE'Then Begin
     CompileOutput:=oDisk;
    End
     Else
    If Copy(StrToUpper(ParamStr(I)),9,255)='DISK'Then Begin
     CompileOutput:=oDisk;
    End
     Else
    Begin
     WriteLn('ParamŠtre de sortie non reconnu !');
     Halt;
    End;
   End
    Else
   Path:=ParamStr(I);
  End;
  OSS.Init(path);
  OSS.Get(sym);
  Module;
  If Not(OSS.Error)Then Begin
   If(CompileOutput=oDisk)Then Begin
    {$I-}Assign(FileOutput,Path2NoExt(Path)+'.BIN');
    Rewrite(FileOutput,1);{$I+}
    If IoResult<>0 Then Begin
     WriteLn('Impossible d''‚crire le fichier binaire : ',Path2NoExt(Path)+'.BIN');
     Halt;
    End;
    BlockWrite(FileOutput,Code,PC*4,ByteWrited);
    System.Close(FileOutput);
   End;
   If(FlagDecode)Then Decode;
   OSG.Execute;
  End;
 End;
END.
