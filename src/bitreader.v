(*===========================================================================
    Bit-reader monad

    This is a trivial free monad for sequences of bools, with no functionality
    beyond bind and retn.

    We also provide an implementation in terms of BYTE readers.
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool finfun fintype ssrnat eqtype seq tuple div.
Require Import bitsrep bitsprops bitsops bitsopsprops cursor monad reader.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Term representation for a T-reader *)
Inductive BitReaderTm T := 
| bitReaderRetn (x: T)
| bitReaderNext (rd: bool -> BitReaderTm T).

Class BitReader T := getBitReaderTm : BitReaderTm T.
Definition readNext {T} {R: BitReader T}: BitReader T := R.

Fixpoint bitReaderBind X Y (r: BitReader X) (f: X -> BitReader Y) : BitReader Y :=
  match r with
  | bitReaderRetn r => f r
  | bitReaderNext rd => bitReaderNext (fun b => bitReaderBind (rd b) f)
  end.

Instance bitReaderMonadOps : MonadOps BitReader :=
{ retn := bitReaderRetn
; bind := bitReaderBind }.

Instance bitReaderMonad : Monad BitReader. 
Proof. apply Build_Monad. 
(* id_l *)
  done. 
(* id_r *)
  move => X. elim => //. 
  - move => rd IH/=.
    apply f_equal. apply functional_extensionality => b. apply IH. 
(* assoc *)
  move => X Y Z. elim => //. 
  - move => rd IH f g/=. 
    apply f_equal. apply functional_extensionality => b. apply IH.
Qed. 

(* We represent a "cursor" for reading and writing bits by a 35-bit value in which the 
   most significant 32 bits are the address of a byte, and the least significant 3 bits 
   are the index of the current bit that we are reading, with 0 representing the *most* 
   significant bit and 7 the least significant (this is the opposite to our usual 
   ordering) *)
Definition BitCursor := Cursor 35. 

(* Functional interpretation of bitReader on sequences. Returns the
   final position, the tail of the given sequence and the value
   read. *)
Fixpoint runBitReader T (r:BitReader T) (c: BitCursor) xs: option (BitCursor * seq bool * T):=
  match r with
  | bitReaderRetn x => Some (c, xs, x)
  | bitReaderNext rd => 
    if c is mkCursor p
    then
      if xs is x::xs 
      then runBitReader (rd x) (next p) xs 
      else None
    else None
  end.

Instance readBit : BitReader bool :=  
  bitReaderNext (fun b => bitReaderRetn b).

Lemma runBitReader_bind T U (r: BitReader T) (f: T -> BitReader U) :
  forall x xs ys cursor cursor', 
  runBitReader r cursor xs = Some (cursor', ys, x) ->
  runBitReader (bitReaderBind r f) cursor xs = runBitReader (f x) cursor' ys.
Proof. induction r.  
+ move => x' xs ys c c' H. simpl in H. by injection H => -> -> ->. 
+ move => x xs ys c c' H'. simpl.
  destruct c => //. 
  destruct xs => //. simpl in H'. by apply H.  
Qed. 

Lemma runBitReader_bindNone T U (r: BitReader T) (f: T -> BitReader U) :
  forall xs cursor, 
  runBitReader r cursor xs = None ->
  runBitReader (bitReaderBind r f) cursor xs = None.
Proof. induction r.  
+ move => xs H. by simpl in H. 
+ move => xs cursor H'.
  destruct cursor => //. 
  destruct xs => //. simpl in H'. 
  by apply H. 
Qed. 

Definition fromByteCursor (c: Cursor 32) : BitCursor := widenCursor 3 c. 

(* We can use a byte-reader to implement a bit-reader by accumulating the bits of the
   next byte read in a list. Notice the use of reverse: we read bits from msb to lsb. *)
Fixpoint bitReaderToReader t (br: BitReader t) bits : Reader (seq bool * t) :=
match br with
| bitReaderRetn x => readerRetn (bits,x)
| bitReaderNext f =>
  if bits is bit::bits'
  then bitReaderToReader (f bit) bits'
  else
    let! byte = readBYTE;
    let (hi,lo) := splitmsb byte in
    bitReaderToReader (f hi) (rev lo)
end.

(* Convert a sequence of bytes into a sequence of bits, reversing the
   order of bits in each byte *)
Fixpoint toBin (s: seq BYTE) : seq bool :=
  if s is b::rest
  then rev (val b)++toBin rest
  else nil.

(* Convert a sequence of bits into a sequence of bytes and a residue
   of bits smaller than a byte *)
Fixpoint fromBin (s: seq bool) : seq bool * seq BYTE :=
  if s is b7::b6::b5::b4::b3::b2::b1::b0::rest
  then let (resbits, bytes) := fromBin rest
       in (resbits, [tuple b0;b1;b2;b3;b4;b5;b6;b7] :: bytes)
  else (s, nil).

(* Relate the sizes of bit and byte sequences across translation *)
Lemma size_toBin s : size (toBin s) = size s * 8.
Proof. induction s => //=. by rewrite size_cat IHs size_rev size_tuple mulSn. Qed.

Lemma size_fromBin bytes : 
  forall bits resbits, 
  fromBin bits = (resbits, bytes) ->
  size resbits = size bits %% 8 /\ size bytes = size bits %/ 8.
Proof. 
induction bytes => bits resbits /= EQ.
+ do 8 (destruct bits; first by injection EQ => <-). simpl in EQ; by destruct (fromBin bits). 
+ do 8 (destruct bits => //). 
  simpl in EQ. case E: (fromBin bits) => [resbits' bytes']; rewrite E in EQ. 
  injection EQ => [EQ1 EQ2 EQ3]. subst.
  destruct (IHbytes _ _ E) as [I1 I2]. split => /=.
  - by rewrite -2!addn4 -addnA modnDr I1. 
  - rewrite -2!addn4 -addnA divnDr => //. by rewrite I2 divnn addn1.  
Qed.

(* Roundtrip property *)
Lemma toBinFromBin bytes: 
  forall bits resbits, fromBin bits = (resbits, bytes) -> toBin bytes ++ resbits = bits. 
Proof. induction bytes => bits resbits EQ/=. 
+ do 8 (destruct bits; first by injection EQ). simpl in EQ. by destruct (fromBin bits).  
+ do 8 (destruct bits => //=). 
case E: (fromBin bits) => [resbits' bytes']. rewrite /= E/= in EQ. 
injection EQ => [EQ1 EQ2 EQ3]. subst. by rewrite -(IHbytes _ _ E). 
Qed. 

(* Invariant for proof of correctness of bitReaderToReader.
     BBInv bitc bits bytec accbits bytes 
   holds if the bit reader state (bitc,bits) is equivalent 
         to the byte reader state (bytec, accbits, bytes)
*)
Inductive BBInv : Cursor 35 -> seq bool -> Cursor 32 -> seq bool -> seq BYTE -> Prop :=
| BBInvAligned (p: Cursor 32) bytes : 
  BBInv (fromByteCursor p) (toBin bytes) p nil bytes

| BBInvCons (p: DWORD) accbit accbits bytes : 
  size accbits < 7 -> 
  BBInv (p ## fromNat (n:=3) (7 - size accbits)) (accbit::accbits++toBin bytes) 
  (next p) (accbit::accbits) bytes.

Lemma BBInvProp1 (bytec: DWORD) (byte:BYTE) (bytes: seq BYTE) accbit accbits (p:BITS 35) :
  fromByteCursor bytec = mkCursor p  ->
  rev byte = accbit :: accbits ->
  BBInv p (accbit :: accbits ++ toBin bytes) bytec [::] (byte :: bytes) ->
  BBInv (next p) (accbits ++ toBin bytes) (next bytec) accbits bytes.
Proof. move => E1 E2 INV.
rewrite /fromByteCursor in E1.
have SIZELO: size accbits = 7. 
have: size (rev byte) = 8 by rewrite size_rev size_tuple. rewrite E2/=; congruence.
destruct accbits => //. 
injection E1 => <-. simpl.
replace (zero 3) with (fromNat (n:=3) 0). 
have NC := @nextCat 32 3 bytec 0. rewrite NC => //. 
simpl in SIZELO. injection SIZELO => SIZEACCBITS.   
replace (fromNat (n:=3) 1) with (fromNat (n:=3) (7 - size accbits)). 
apply BBInvCons. by rewrite SIZEACCBITS. by rewrite SIZEACCBITS. 
by rewrite fromNat0.
Qed.

Lemma BBInvProp2 (p: DWORD) bytes accbit accbits :
  size accbits < 7 ->
  BBInv (p ## fromNat (n:=3) (7 - size accbits)) (accbit :: accbits ++ toBin bytes)
          (next p) (accbit :: accbits) bytes ->
  BBInv (next (p ## fromNat (n:=3) (7 - size accbits))) (accbits ++ toBin bytes)
     (next p) accbits bytes.
Proof. move => LT INV.
destruct accbits. rewrite /= subn0. 
replace (fromNat (n:=3) 7) with (ones 3). rewrite nextCatNext. apply BBInvAligned.
apply toNat_inj. by rewrite toNat_ones toNat_fromNat. 
have: next (p ## fromNat (n:=3) (6 - size accbits)) = p ## fromNat (n:=3) (7 - size accbits). 
apply cursorToNat_inj. rewrite cursorToNat_next /=. 
rewrite 2!toNatCat 2!toNat_fromNat.
rewrite modn_small. rewrite modn_small. rewrite -addn1 -addnA addn1. rewrite -subSn.  
done. simpl in LT. rewrite ltnS in LT. by apply ltnW. 
by rewrite ltnS/= leq_subr.
apply ltnW.  
rewrite ltnS/= ltnS/=. apply leq_subr. move => ->. apply BBInvCons. by apply ltnW. 
Qed. 


Lemma bitReaderToReader_correctAux t (br: BitReader t) :
  forall bitc bits bytec accbits bytes bitc' bits' v,
  runBitReader br bitc bits = Some (bitc', bits', v) ->
  BBInv bitc bits bytec accbits bytes ->  
  exists bytec' accbits' bytes',
  runReader (bitReaderToReader br accbits) bytec bytes = 
    Some(bytec',bytes',(accbits',v)) /\ BBInv bitc' bits' bytec' accbits' bytes'.
Proof. induction br => bitc bits bytec accbits bytes bitc' bits' v RBR INV.
+ exists bytec, accbits, bytes. injection RBR => <- <- <-. intuition. 
+ inversion INV; subst.
  (* No accumulated bits *)
  - case Ebytes: bytes => [| byte bytes']; subst. 
    (* No bytes, so we should fail *)
    * by destruct bytec => //.  
    (* At least one byte *)
    * rewrite /= in RBR.
      case E: (splitmsb byte) => [hi lo]. 
      have EE := splitmsb_rev E. 
      rewrite EE/= in RBR. 
      case E': (fromByteCursor bytec) => [p |]; rewrite E' in RBR, INV => //. 
      rewrite /bitReaderToReader-/bitReaderToReader.      
      have SZ: size (rev lo) < 8 by rewrite size_tuple.
      destruct bytec => //. 
      specialize (H hi _ _ (next p0) (rev lo) bytes' _ _ _ RBR).  
      rewrite /=EE/= in INV.
      have INV' := BBInvProp1 E' EE INV.
      specialize (H INV'). 
      destruct H as [bytec' [accbits' [bytes'' [H2 H3]]]].
      exists bytec', accbits', bytes''. 
      split => //. erewrite runReader_bind. rewrite E. apply H2.
      rewrite runReader_readBYTE. reflexivity. 

  (* At least one accumulated bit *)
  - have LT': size accbits0 < 8. apply ltnW. by apply: H0.
    rewrite /fromByteCursor in RBR. 
    apply: (H accbit _ _ (next p) accbits0 bytes _ _ _ RBR).
    apply: BBInvProp2 INV => //.  
Qed.     

(* Note that if bits is non-null then the byte cursor is already advanced to the next 
   location *)
Definition bitCursorAndBitsToByteCursor (c:Cursor 35) (bits:seq bool) : Cursor 32 :=
  if c is mkCursor p then if bits is nil then mkCursor (@high 32 3 p) 
                          else next (@high 32 3 p) else top _.

Corollary bitReaderToReader_correct t (br: BitReader t) :
  forall bytes resbits (cursor: Cursor 32) (cursor':Cursor 35) v,
  runBitReader br (fromByteCursor cursor) (toBin bytes) = Some (cursor', resbits, v) ->
  exists resbytes, exists resbits', 
  runReader (bitReaderToReader br nil) cursor bytes = 
    Some(bitCursorAndBitsToByteCursor cursor' resbits',resbytes,(resbits',v))
  /\ resbits = resbits' ++ toBin resbytes.
Proof. move => bytes resbits cursor cursor' v RBR. 
have BRR:= bitReaderToReader_correctAux RBR (BBInvAligned _ _).
destruct BRR as [bytec' [accbits' [bytes' [H1 H2]]]]. 
exists bytes', accbits'. rewrite H1. inversion H2; subst.
+ split => //. rewrite /bitCursorAndBitsToByteCursor/fromByteCursor. 
  destruct bytec' => //. rewrite /widenCursor. by rewrite high_catB. 
+ split => //. by rewrite /bitCursorAndBitsToByteCursor high_catB. 
Qed. 



