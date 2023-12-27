{ @author: Sylvain Maltais (support@gladir.com)
  @source: Bas‚ sur le livre "Compiler Construction" de Niklaus Wirth's
  @created: 2023
  @website(https://www.gladir.com/CODER/OBERON-TP)
  @abstract(Target: Turbo Pascal 7, Free Pascal 3.2)
}

Unit OSS;

INTERFACE

Const
  IdLen = {16}32;
  KW=33;
  MaxInt = 2147483647;

 (* Symbole lexicale de Oberon *)
Const
 _NULL=0;
 _TIMES=1;
 _DIV=3;
 _MOD=4;
 _AND=5;
 _PLUS=6;
 _MINUS=7;
 _OR=8;
 _EQUAL=9;
 _NEQ=10;
 _LESS=11;
 _LEQ=12;
 _GTR=13;
 _GEQ=14;
 _IN=15;
 _IS=16;
 _ARROW=17;
 _PERIOD=18;
 _CHAR=20;
 _INT=21;
 _FALSE=23;
 _TRUE=24;
 _NIL=25;
 _NOT=27;
 _LPAREN=28;
 _LBRAKET=29;
 _LBRACE=30;
 _IDENT=31;
 _IF=32;
 _WHILE=34;
 _REPEAT=35;
 _CASE=36;
 _FOR=37;
 _COMMA=40;
 _COLON=41;
 _BECOMES=42;
 _RPARENT=44;
 _RBRAKET=45;
 _RBRACE=46;
 _THEN=47;
 _OF=48;
 _DO=49;
 _TO=50;
 _BY=51;
 _SEMICOLON=52;
 _END=53;
 _BAR=54;
 _ELSE=55;
 _ELSIF=56;
 _UNTIL=57;
 _RETURN=58;
 _ARRAY=60;
 _RECORD=61;
 _POINTER=62;
 _CONST=63;
 _TYPE=64;
 _VAR=65;
 _PROCEDURE=66;
 _BEGIN=67;
 _IMPORT=68;
 _MODULE=69;
 _DEFINITION=70;
 _EOF=71;

Type
 Ident=Array[0..IdLen] of Char;

Var
 Val:LongInt;
 Id:Ident;
 Error:Boolean;
 Pos:Integer;

 Ch:Char;
 IsEOF:Boolean;
 ErrPos:LongInt;
 FileVar:Text;

Procedure Mark(Msg:String);
Procedure Identifier(Var Sym:Integer);
Procedure Number(Var Sym:Integer);
Procedure Comment;
Procedure Get(Var Sym:Integer);
Procedure Init(Path:String);

IMPLEMENTATION

Uses Strings;

Const
 keyTab:Array[0..KW] of Record
  Sym:Integer;
  id:String[12];
 End=(
  (Sym:_ARRAY;Id:'ARRAY'),
  (Sym:_BEGIN;Id:'BEGIN'),
  (Sym:_BY;Id:'BY'),
  (Sym:_CASE;Id:'CASE'),
  (Sym:_CONST;Id:'CONST'),
  (Sym:_DEFINITION;Id:'DEFINITION'),
  (Sym:_DIV;Id:'DIV'),
  (Sym:_DO;Id:'DO'),
  (Sym:_ELSE;Id:'ELSE'),
  (Sym:_ELSIF;Id:'ELSIF'),
  (Sym:_END;Id:'END'),
  (Sym:_FALSE;Id:'FALSE'),
  (Sym:_FOR;Id:'FOR'),
  (Sym:_IF;Id:'IF'),
  (Sym:_IMPORT;Id:'IMPORT'),
  (Sym:_IN;Id:'IN'),
  (Sym:_IS;Id:'IS'),
  (Sym:_MOD;Id:'MOD'),
  (Sym:_MODULE;Id:'MODULE'),
  (Sym:_NIL;Id:'NIL'),
  (Sym:_OF;Id:'OF'),
  (Sym:_OR;Id:'OR'),
  (Sym:_POINTER;Id:'POINTER'),
  (Sym:_PROCEDURE;Id:'PROCEDURE'),
  (Sym:_RECORD;Id:'RECORD'),
  (Sym:_REPEAT;Id:'REPEAT'),
  (Sym:_RETURN;Id:'RETURN'),
  (Sym:_THEN;Id:'THEN'),
  (Sym:_TO;Id:'TO'),
  (Sym:_TRUE;Id:'TRUE'),
  (Sym:_TYPE;Id:'TYPE'),
  (Sym:_UNTIL;Id:'UNTIL'),
  (Sym:_VAR;Id:'VAR'),
  (Sym:_WHILE;Id:'WHILE')
 );

Procedure ReadChar;Begin
 Read(FileVar,Ch);
 If IOResult<>0 Then Begin
  Ch:=#0;
  IsEOF:=TRUE;
 End;
 Inc(Pos);
End;

Procedure Mark(Msg:String);
Var
 P:LongInt;
Begin
 P:=Pos;
 If P>ErrPos Then Begin
  WriteLn('  position ', p, ': ',Msg);
 End;
 ErrPos:=P;
 Error:=True;
End;

Procedure Identifier(Var sym:Integer);
Var
 i,k:Integer;
 StrId:String;
Begin
 i:=0;
 Repeat
  If i<IdLen Then Begin
   id[i]:=ch;
   Inc(i);
  End;
  ReadChar;
 Until(ch<'0')or(Ch>'9')and(Ch<'A')or(ch>'Z')and(ch<'a')or(ch>'z');
 id[i]:=#0;
 StrId:=StrPas(Id);
 Sym:=_IDENT;
 For K:=0 to High(keyTab) do Begin
  If(StrId=keyTab[k].id)Then Begin
   Sym:=keyTab[k].Sym;
   Break;
  End;
 End;
End;

Procedure Number(Var Sym:Integer);Begin
 Val:=0;
 Sym:=_INT;
 Repeat
  If Val<=(MaxInt-Ord(ch)+Ord('0')) div 10 Then Val:=10*Val+(Ord(ch)-Ord('0'))
   Else
  Begin
   Mark('Nombre trop large');
   Val:=0;
  End;
  ReadChar;
 Until(Ch<'0')or(Ch>'9');
End;

Procedure Comment;Begin
 Repeat
  Repeat
   ReadChar;
   While Ch='(' do Begin
    ReadChar;
    If Ch='*'Then Comment;
   End;
  Until(Ch='*')or IsEOF;
  Repeat
   ReadChar;
  Until(Ch<>'*')or IsEOF;
 Until(Ch=')')or IsEOF;
 If Not IsEOF Then Begin
  ReadChar;
 End
  Else
 Begin
  Mark('Le commentaire n''est pas termin‚');
 End;
End;

Procedure Get(Var Sym:Integer);Begin
 Repeat
  While Not IsEOF and((Ch<=' ')or(Ch>=#$7F))do ReadChar;
  If IsEOF Then sym:=_EOF Else
  Case Ch of
   '!','%','''','?','@','\','_','`':Begin
    ReadChar;
    Sym:=_NULL;
   End;
   '"':Begin
    ReadChar;
    Val:=ORD(ch);
    Repeat
     ReadChar;
    Until (Ch='"') OR IsEOF;
    ReadChar;
    Sym:=_CHAR;
   End;
   '#':Begin
    ReadChar;
    Sym:=_NEQ;
   End;
   '&':Begin
    ReadChar;
    Sym:=_AND;
   End;
   '(':Begin
    ReadChar;
    If Ch='*'Then Begin
     Sym:=_NULL;
     Comment;
    End
     Else
    Sym:=_LPAREN;
   End;
   ')':Begin
    ReadChar;
    Sym:=_RPARENT;
   End;
   '*':Begin
    ReadChar;
    Sym:=_TIMES;
   End;
   '+':Begin
    ReadChar;
    sym:=_PLUS;
   End;
   ',':Begin
    ReadChar;
    sym:=_COMMA;
   End;
   '-':Begin
    ReadChar;
    Sym:=_MINUS;
   End;
   '.':Begin
    ReadChar;
    Sym:=_PERIOD;
   End;
   '/':Begin
    ReadChar;
    Sym:=_NULL;
   End;
   '0'..'9':Number(sym);
   ':':Begin
    ReadChar;
    If Ch='='Then Begin
     ReadChar;
     Sym:=_BECOMES;
    End
     Else
    Sym:=_COLON;
   End;
   ';':Begin
    ReadChar;
    Sym:=_SEMICOLON;
   End;
   '<':Begin
    ReadChar;
    If Ch='='Then Begin
     ReadChar;
     Sym:=_LEQ;
    End
     Else
    Begin
     Sym:=_LESS;
    End;
   End;
   '=':Begin
    ReadChar;
    Sym:=_EQUAL;
   End;
   '>':Begin
    ReadChar;
    If Ch='='Then Begin
     ReadChar;
     Sym:=_GEQ;
    End
     Else
    Begin
     Sym:=_GTR;
    End;
   End;
   'a'..'z','A'..'Z':Identifier(sym);
   '[':Begin
    ReadChar;
    Sym:=_LBRAKET;
   End;
   ']':Begin
    ReadChar;
    Sym:=_RBRAKET;
   End;
   '^':Begin
    ReadChar;
    Sym:=_NULL;
   End;
   '{':Begin
    ReadChar;
    Sym:=_RBRACE;
   End;
   '}':Begin
    ReadChar;
    Sym:=_LBRACE;
   End;
   '|':Begin
    ReadChar;
    Sym:=_BAR;
   End;
   '~':Begin
    ReadChar;
    Sym:=_NOT;
   End;
   Else Begin
    ReadChar;
    Sym:=_NULL;
   End;
  End;
 Until Sym<>_NULL;
End;

Procedure Init(path:String);Begin
 Error:=False;
 ErrPos:=-1;
 Pos:=0;
 IsEOF:=False;
 {$I-}Assign(FileVar,Path);
 Reset(FileVar);{$I+}
 If IOResult=0 Then Begin
  ReadChar;
 End
  Else
 Begin
  Error:=True;
  IsEOF:=True;
  Mark('Fichier introuvable');
  Halt;
 End;
End;

BEGIN
 Error:=True;
END.
