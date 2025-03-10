datatype State = | Initial1| Error1| Error2| Done1
datatype LastOp = None | Read | Write


datatype Variables = Variables(
  count:nat,
  success:nat,
  lastop:LastOp,
  state:State
)

predicate Init(v:Variables)
{
  && v.state == Initial1
  && v.count > 0
  && v.lastop == None
  && v.success == 0
}

predicate TransitionFromInitial1ToError1withwrite (v:Variables, v':Variables)
  requires Valid(v)
{
  && v.state == Initial1
  && v'.state == Error1
  && v'.count == v.count - 1
  && v.lastop != Write
  && v'.lastop == Write
  && v'.success == v.success == 0
}

predicate TransitionFromError1ToError2withread (v:Variables, v':Variables)
  requires Valid(v)
{
  && v.state == Error1
  && v'.state == Error2
  && v'.count == v.count - 1
  && v'.lastop == Read
  && v'.success == v.success == 0
}

predicate TransitionFromError2ToError2withread (v:Variables, v':Variables)
  requires Valid(v)
{
  && v.state == Error2
  && v'.state == Error2
  && v'.count == v.count - 1
  && v'.lastop == Read
  && v'.success == v.success == 0
}

predicate TransitionFromError2ToDone1withread (v:Variables, v':Variables)
  requires Valid(v)
{
  && v.state == Error2
  && v'.state == Done1
  && v'.count == v.count - 1
  && v'.lastop == Read
  && v'.success == v.success + 1
}

predicate TransitionFromError2ToInitial1withread (v:Variables, v':Variables)
  requires Valid(v)
{
  && v.state == Error2
  && v'.state == Initial1
  && v'.count == v.count - 1
  && v'.lastop == Read
  && v'.success == v.success == 0
}

predicate TransitionFromInitial1ToDone1withwrite (v:Variables, v':Variables)
  requires Valid(v)
{
  && v.state == Initial1
  && v'.state == Done1
  && v'.count == v.count - 1
  && v.lastop != Write
  && v'.lastop == Write
  && v'.success == v.success + 1
}

predicate TransitionFromError1ToDone1withread (v:Variables, v':Variables)
  requires Valid(v)
{
  && v.state == Error1
  && v'.state == Done1
  && v'.count == v.count - 1
  && v'.lastop == Read
  && v'.success == v.success + 1
}

predicate TransitionFromError1ToInitial1withread (v:Variables, v':Variables)
  requires Valid(v)
{
  && v.state == Error1
  && v'.state == Initial1
  && v'.count == v.count - 1
  && v'.lastop == Read
  && v'.success == v.success == 0
}

predicate TransitionFromError1ToDone1withwrite (v:Variables, v':Variables)
  requires Valid(v)
{
  && v.state == Error1
  && v'.state == Done1
  && v'.count == v.count - 1
  && v.lastop == Write
  && v'.lastop == None
  && v'.success == v.success + 1
}

datatype Step = 
  | TransitionFromInitial1ToError1withwriteStep()
  | TransitionFromError1ToError2withreadStep()
  | TransitionFromError2ToError2withreadStep()
  | TransitionFromError2ToDone1withreadStep()
  | TransitionFromError2ToInitial1withreadStep()
  | TransitionFromInitial1ToDone1withwriteStep()
  | TransitionFromError1ToDone1withreadStep()
  | TransitionFromError1ToInitial1withreadStep()
  | TransitionFromError1ToDone1withwriteStep()

predicate NextStep(v:Variables, v':Variables, step:Step)
  requires Valid(v)
{
  match step
	  case TransitionFromInitial1ToError1withwriteStep() => TransitionFromInitial1ToError1withwrite(v, v')
	  case TransitionFromError1ToError2withreadStep() => TransitionFromError1ToError2withread(v, v')
	  case TransitionFromError2ToError2withreadStep() => TransitionFromError2ToError2withread(v, v')
	  case TransitionFromError2ToDone1withreadStep() => TransitionFromError2ToDone1withread(v, v')
	  case TransitionFromError2ToInitial1withreadStep() => TransitionFromError2ToInitial1withread(v, v')
	  case TransitionFromInitial1ToDone1withwriteStep() => TransitionFromInitial1ToDone1withwrite(v, v')
	  case TransitionFromError1ToDone1withreadStep() => TransitionFromError1ToDone1withread(v, v')
	  case TransitionFromError1ToInitial1withreadStep() => TransitionFromError1ToInitial1withread(v, v')
	  case TransitionFromError1ToDone1withwriteStep() => TransitionFromError1ToDone1withwrite(v, v')
}

predicate Next(v:Variables, v':Variables)
  requires Valid(v)
{
  exists step :: NextStep(v, v', step)
}

predicate Valid(v:Variables)
{
    && (( || v.state == Initial1 || v.state == Error1 || v.state == Error2) ==> (v.success == 0))
    && ((v.state == Done1) ==> (v.success == 1))
}

predicate ValidTransition(v:Variables, v':Variables)
{
    && v'.success - v.success <= 1
    && v.count - v'.count == 1
    && (v.lastop == Write ==> v'.lastop != Write)
}

lemma SafetyProof()
  ensures forall v | Init(v) :: Valid(v)
  ensures forall v, v' | (Valid(v) && Next(v, v')) :: Valid(v') && (ValidTransition(v,v'))
{
}

type Trace = nat -> Variables

ghost predicate IsTrace(trace: Trace)
{
    Init(trace(0)) &&
    forall i: nat :: (Valid(trace(i)) && Next(trace(i), trace(i+1)))
}

lemma SafetyProofTrace(trace: Trace)
    requires Init(trace(0))
{
    // Base case:
    assert Init(trace(0));
    assert Valid(trace(0));

    assert Next(trace(0), trace(1)) ==> Valid(trace(1)) && ValidTransition(trace(0), trace(1));
    // assert Valid(trace(1)) && Next(trace(1), trace(2)) ==> Valid(trace(2)) && ValidTransition(trace(1), trace(2));

    // Inductive step:
    forall i | i >= 0
      ensures (Valid(trace(i)) && Next(trace(i), trace(i+1))) ==> (Valid(trace(i+1)) && ValidTransition(trace(i), trace(i+1)))
    {
      if Valid(trace(i)) && Next(trace(i), trace(i+1)){
        assert trace(i).success <= 1;
        if trace(i+1).state == Done1 {
          assert trace(i+1).success == 1;
        }
      }
      // assert Valid(trace(i)) && Next(trace(i), trace(i+1)) ==> Valid(trace(i+1)) && ValidTransition(trace(i), trace(i+1));
      // if Valid(trace(i)) && Next(trace(i), trace(i+1)) && Valid(trace(i+1)) && ValidTransition(trace(i), trace(i+1)) {
      //     assert trace(i).count > trace(i+1).count;
      //     assert trace(i+1).success <= 1;
      // }
    }
}

// Assume that the network errors will eventually correct
ghost predicate FairNetwork(trace: Trace) 
{
    IsTrace(trace) &&
    forall n: nat :: HasDone(n, trace)
}

ghost predicate HasDone(n: nat, trace: Trace)
{
    exists n' :: n <= n' && trace(n').state == Done1 && trace(n').success == 1
}

lemma LivenessProof(trace: Trace, n: nat)
      returns (n': nat)
    requires IsTrace(trace) && FairNetwork(trace)
    requires Init(trace(n))
    requires forall i: nat :: i >= n ==> (Valid(trace(i)) && Next(trace(i), trace(i+1)))
    ensures n <= n' && trace(n').state == Done1 && trace(n').success == 1
{
      n' := n;
    while true
      invariant n <= n'
      invariant (Valid(trace(n)) && Next(trace(n), trace(n+1)))
      invariant Valid(trace(n')) && Next(trace(n'), trace(n'+1)) && ValidTransition(trace(n'), trace(n'+1)) && Valid(trace(n'+1))
      decreases if Valid(trace(n')) && Next(trace(n'), trace(n'+1)) && Valid(trace(n'+1)) && ValidTransition(trace(n'), trace(n'+1)) then trace(n').count else 0
    {
      SafetyProofTrace(trace);
      var prev := trace(n').count;
      var prev_n := n';

      n' := n' + 1;

      assert trace(n').count < prev;

      if trace(n').state == Done1 {
        assert trace(n').success == 1;
        break;
      }
    }
    assert trace(n').state == Done1;
    assert trace(n').success == 1;
}

