package freeboogie.vcgen;

import java.util.*;

import com.google.common.collect.*;
import genericutils.*;

import freeboogie.ast.*;
import freeboogie.tc.*;

/**
  Gets rid of assignments and "old" expressions by introducing 
  new variables. We assume that
    (0) break, while, if-s are desugared,
    (1) specs are desugared,
    (2) calls are desugared,
    (3) havocs are desugared,
    (4) the flowgraphs are computed and have no cycles.
 
  Each variable X is transformed into a sequence of variables
  X, X_1, X_2, ... Each command has a read index r and a write
  index w (for each variable), meaning that reads from X will be
  replaced by reads from X_r and a write to X is replaced by a
  write to X_w.
 
  Copy operations (assumes) need to be inserted when the value
  written by a node is not the same as the one read by one of
  its successors (according the the scheme above).

  The read and write indexes are attached to commands by
  subclasses when the functions {@code readIndex(cmd, cache)}
  and {@code writeIndex(cmd, cache)} are called.

  Subclasses *may*:
    - find the parents and the children of a command using
      {@code parents(cmd)} and {@code children(cmd)}
    - find if a command reads or writes using {@code reads(cmd)}
      and {@code writes(cmd)}
  Subclasses *must*:
    - store the results they compute in the caches that are
      accessed using {@code readIndexCache()} and {@code 
      writeIndexCache()}

  @author rgrig
 */
public abstract class AbstractPassivator extends Transformer {
  /*
    The code
      [LA] : CA
      [LB] : CB
    is transformed into
      [LA]: CA
      L:    getCopyCommands(CA, CB)
      [LB]: CB
    Square brackets indicate that labels may be missing and L is
    a fresh label, unused in this case. The function getCopyCommands
    is called while visiting the command CA, its result is stored
    in trailingCommands, and these are finally inserted in the
    block while visiting the block.

    The code
      [LA]: goto LB, [LC]
      ...
      LB:   CB
    is transformed into
      [LA]: goto L, [LC]
      ...
      LB:   CB
      ...
      L:    getCopyCommands(CA, CB)
            goto LB
    The new commands are computed while visiting the command CA
    (goto LB, ...) and added to endOfBodyCommands. They are picked up
    from there and inserted at the end of the body's block while
    visiting the body. At that time we also must make sure that the
    old body block finished with "return" so that the copy commands
    we insert at the end don't spoil the flow of control.

    Assignments
      x := e
    are transformed into assumptions
      assume x$$3 == e[x->x$$2, y->y$$7]
    Renaming could be done here and adding assume could be done in
    a different transformer if this one gets big.
   */
  private HashMap<VariableDecl, HashMap<Command, Integer>> readIdx;
  private HashMap<VariableDecl, HashMap<Command, Integer>> writeIdx;
  private HashMap<VariableDecl, Integer> toReport;

  private Command currentCommand;
  private VariableDecl currentVar;
  private HashSet<VariableDecl> allWritten; // by the current implementation
  private ImmutableList.Builder<VariableDecl> newLocals;

  private ArrayDeque<Command> trailingCommands = new ArrayDeque<Command>();
  private ArrayDeque<Command> endOfBodyCommands = new ArrayDeque<Command>();

  private int belowOld;
  private boolean inResults;

  // === used by subclasses ===
  private HashMap<VariableDecl, Integer> newVarsCnt;
  private HashMap<Command, HashSet<VariableDecl>> commandWs;
  private HashMap<Command, HashSet<VariableDecl>> commandRs;
  private ReadWriteSetFinder rwsf;
  private HashMap<Command, Integer> currentReadIdxCache;
  private HashMap<Command, Integer> currentWriteIdxCache;
  private SimpleGraph<Command> currentFG;

  abstract int computeReadIndex(Command c);
  abstract int computeWriteIndex(Command c);

  Set<Command> parents(Command c) {
    return currentFG.from(c);
  }

  Set<Command> children(Command c) {
    return currentFG.to(c);
  }

  boolean writes(Command c) {
    HashSet<VariableDecl> ws = commandWs.get(c);
    if (ws == null) {
      ws = Sets.newLinkedHashSet();
      for (VariableDecl vd : rwsf.get(c).second) ws.add(vd);
      commandWs.put(c, ws);
    }
    return ws.contains(currentVar);
  }

  boolean reads(Command c) {
    HashSet<VariableDecl> rs = commandRs.get(c);
    if (rs == null) {
      rs = Sets.newLinkedHashSet();
      for (VariableDecl vd : rwsf.get(c).first) rs.add(vd);
      commandRs.put(c, rs);
    }
    return rs.contains(currentVar);
  }

  Map<Command, Integer> readIndexCache() {
    return currentReadIdxCache;
  }

  Map<Command, Integer> writeIndexCache() {
    return currentWriteIdxCache;
  }

  // === transformers ===

  // visits ONLY implementations and then adds new globals
  @Override public Program eval(Program program) {
    ImmutableList<Implementation> implementations = program.implementations();
    ImmutableList<VariableDecl> variables = program.variables();
    readIdx = Maps.newHashMap();
    writeIdx = Maps.newHashMap();
    newVarsCnt = Maps.newHashMap();
    toReport = Maps.newHashMap();
    commandWs = Maps.newHashMap();
    rwsf = new ReadWriteSetFinder(tc.st());
    implementations = AstUtils.evalListOfImplementation(implementations, this);
    if (!newVarsCnt.isEmpty()) {
      ImmutableList.Builder<VariableDecl> newVariables = 
          ImmutableList.builder();
      newVariables.addAll(variables);
      for (Map.Entry<VariableDecl, Integer> e : newVarsCnt.entrySet()) {
        for (int i = 1; i <= e.getValue(); ++i) {
          newVariables.add(VariableDecl.mk(
              ImmutableList.<Attribute>of(),
              name(e.getKey().name(), i),
              e.getKey().type().clone(), 
              AstUtils.cloneListOfIdentifier(e.getKey().typeArgs()),
              null));
        }
      }
      variables = newVariables.build();
    }
    return Program.mk(
        program.fileName(),
        program.types(),
        program.axioms(),
        variables,
        program.constants(),
        program.functions(),
        program.procedures(),
        implementations,
        program.loc());
  }

  @Override public Implementation eval(Implementation implementation) {
    Body body = implementation.body();
    Signature sig = implementation.sig();
    currentFG = tc.flowGraph(implementation);
    if (currentFG.hasCycle()) {
      Err.warning("" + implementation.loc() + ": Implementation " + 
        sig.name() + " has cycles. I'm not passivating it.");
      return implementation;
    }
    
    // collect all variables that are assigned to
    Pair<CSeq<VariableDecl>, CSeq<VariableDecl>> rwIds = 
        implementation.eval(rwsf);
    allWritten = Sets.newLinkedHashSet();
    for (VariableDecl vd : rwIds.second) allWritten.add(vd);

    // figure out read and write indexes
    for (VariableDecl vd : allWritten) {
      currentVar = vd;
      currentReadIdxCache = Maps.newLinkedHashMap();
      currentWriteIdxCache = Maps.newLinkedHashMap();
      readIdx.put(vd, currentReadIdxCache);
      writeIdx.put(vd, currentWriteIdxCache);
      currentFG.iterNode(new Closure<Command>() {
        @Override public void go(Command c) {
          computeReadIndex(c);
          computeWriteIndex(c);
        }
      });
      Integer maxVersion = newVarsCnt.get(currentVar);
      if (maxVersion == null) maxVersion = 0;
      for (int version : currentWriteIdxCache.values()) 
        maxVersion = Math.max(maxVersion, version);
      newVarsCnt.put(currentVar, maxVersion);
    }

    // transform the body and the out parameters
    belowOld = 0;
    newLocals = ImmutableList.builder();
    body = (Body) body.eval(this); // adds to newLocals
    sig = (Signature) sig.eval(this); // adds to newLocals
    newLocals.addAll(body.vars());
    body = Body.mk(newLocals.build(), body.block(), body.loc());
    return Implementation.mk(
        implementation.attributes(), 
        sig, 
        body,
        implementation.loc());
  }

  @Override public Signature eval(Signature signature) {
    ImmutableList<VariableDecl> args = signature.args();
    ImmutableList<VariableDecl> results = signature.results();
    AstUtils.evalListOfVariableDecl(args, this);
    assert !inResults : "There shouldn't be nesting here.";
    inResults = true;
    results = AstUtils.evalListOfVariableDecl(results, this);
    inResults = false;
    return Signature.mk(
        signature.name(), 
        signature.typeArgs(), 
        args, 
        results,
        signature.loc());
  }

  @Override public Body eval(Body body) {
    Block block = body.block();
    endOfBodyCommands.clear();
    block = (Block) block.eval(this);
    ImmutableList<Command> cmds = block.commands();
    ImmutableList.Builder<Command> newCommands = ImmutableList.builder();
    newCommands.addAll(cmds);
    if (cmds.isEmpty() || !isReturn(cmds.get(cmds.size() - 1)))
      newCommands.add(GotoCmd.mk(noString, noString, body.loc()));
    newCommands.addAll(endOfBodyCommands);

    // NOTE: eval(Implementation) will add newLocals to vars
    AstUtils.evalListOfVariableDecl(body.vars(), this);
    return Body.mk(
        body.vars(), 
        Block.mk(newCommands.build(), block.loc()),
        body.loc());
  }

  @Override public Block eval(Block block) {
    ImmutableList.Builder<Command> newCommands = ImmutableList.builder();
    for (Command c : block.commands()) {
      trailingCommands.clear();
      Command nc = (Command) c.eval(this);
      newCommands.add(nc).addAll(trailingCommands);
    }
    return Block.mk(newCommands.build(), block.loc());
  }

  // BEGIN command visitors {{{
  // Note the return type
  @Override public AssertAssumeCmd eval(AssignmentCmd cmd) {
    trailingCommands = getCopyCommands(
        cmd, 
        currentFG.to(cmd).iterator().next());
    assert currentCommand == null : "no nesting";
    currentCommand = cmd;
    Expr assume = BooleanLiteral.mk(BooleanLiteral.Type.TRUE, cmd.loc());
    for (OneAssignment oa : cmd.assignments()) {
      assume = BinaryOp.mk(
          BinaryOp.Op.AND, 
          assume, 
          (Expr) oa.eval(this), 
          cmd.loc());
    }
    AssertAssumeCmd assumeCmd = AssertAssumeCmd.mk(
        cmd.labels(),
        AssertAssumeCmd.CmdType.ASSUME,
        AstUtils.ids(),
        assume,
        cmd.loc());
    currentCommand = null;
    return assumeCmd;
  }

  @Override public Expr eval(OneAssignment oneAssignment) {
    Identifier lhs = oneAssignment.lhs();
    Expr value = (Expr) oneAssignment.rhs().eval(this);
    VariableDecl vd = (VariableDecl)tc.st().ids.def(lhs);
    return BinaryOp.mk(
        BinaryOp.Op.EQ,
        Identifier.mk(
            name(lhs.id(), getIdx(writeIdx, vd)),
            lhs.types(),
            lhs.loc()),
        value,
        oneAssignment.loc());
  }

  @Override public AssertAssumeCmd eval(AssertAssumeCmd assertAssumeCmd) {
    trailingCommands = getCopyCommands(
        assertAssumeCmd, 
        currentFG.to(assertAssumeCmd).iterator().next());
    assert currentCommand == null; // no nesting
    currentCommand = assertAssumeCmd;
    assertAssumeCmd = AssertAssumeCmd.mk(
        assertAssumeCmd.labels(),
        assertAssumeCmd.type(),
        assertAssumeCmd.typeArgs(),
        (Expr) assertAssumeCmd.expr().eval(this),
        assertAssumeCmd.loc());
    currentCommand = null;
    return assertAssumeCmd;
  }

  @Override public void see(BreakCmd breakCmd) {
    assert false : "Break commands are assumed to be desugared at this stage.";
  }

  @Override public GotoCmd eval(GotoCmd gotoCmd) {
    ImmutableList.Builder<String> newSuccessors = ImmutableList.builder();
    for (Command succCmd : currentFG.to(gotoCmd)) {
      String oldTarget = succCmd.labels().get(0);
      ArrayDeque<Command> copyCommands = getCopyCommands(gotoCmd, succCmd);
      if (copyCommands.isEmpty())
        newSuccessors.add(oldTarget);
      else {
        endOfBodyCommands.addAll(copyCommands);
        endOfBodyCommands.add(GotoCmd.mk(
            noString, 
            ImmutableList.of(oldTarget),
            gotoCmd.loc()));
        newSuccessors.add(copyCommands.peekFirst().labels().get(0));
      }
    }
    return GotoCmd.mk(gotoCmd.labels(), newSuccessors.build(), gotoCmd.loc());
  }

  @Override public HavocCmd eval(HavocCmd havocCmd) {
    assert false : "HavocCmd is assumed to be desugared.";
    return havocCmd;
  }

  @Override public CallCmd eval(CallCmd callCmd) {
    assert false : "CallCmd is assumed to be desugared";
    return callCmd;
  }
  // END command visitors }}}

  // BEGIN other visitors {{{
  @Override public Expr eval(OldExpr atomOld) {
    Expr expr = atomOld.expr();
    ++belowOld;
    expr = (Expr)expr.eval(this);
    --belowOld;
    return expr;
  }

  @Override public Identifier eval(Identifier atomId) {
    if (currentCommand == null) return atomId;
    IdDecl d = tc.st().ids.def(atomId);
    if (!(d instanceof VariableDecl)) return atomId;
    VariableDecl vd = (VariableDecl) d;
    int idx = getIdx(readIdx, vd);
    if (idx == 0) return atomId;
    return Identifier.mk(name(atomId.id(), idx), atomId.types(), atomId.loc());
  }

  @Override public VariableDecl eval(VariableDecl variableDecl) {
    Integer last = newVarsCnt.get(variableDecl);
    if (last == null) last = 0;
    newVarsCnt.remove(variableDecl);
    String oldName = variableDecl.name();
    if (inResults) {
      variableDecl = VariableDecl.mk(
          ImmutableList.<Attribute>of(),
          name(oldName, last),
          variableDecl.type(),
          variableDecl.typeArgs(),
          null,
          variableDecl.loc());
    }
    int start = 1;
    if (inResults) {
      --last;
      --start;
    }
    for (int i = start; i <= last; ++i) {
      newLocals.add(VariableDecl.mk(
          ImmutableList.<Attribute>of(),
          name(oldName, i),
          variableDecl.type().clone(), 
          AstUtils.cloneListOfIdentifier(variableDecl.typeArgs()),
          null,
          variableDecl.loc()));
    }
    return variableDecl;
  }
  // END other visitors }}}

  // === helpers ===
  private int getIdx(
      HashMap<VariableDecl, HashMap<Command, Integer> > cache, 
      VariableDecl vd
  ) {
    Map<Command, Integer> m = cache.get(vd);
    if (m == null || belowOld > 0) 
      return 0; // this variable is never written to
    Integer idx = m.get(currentCommand);
    return idx == null? 0 : idx;
  }

  private String name(String prefix, int count) {
    if (count == 0) return prefix;
    return prefix + "$$" + count;
  }

  private ArrayDeque<Command> getCopyCommands(Command ca, Command cb) {
    ImmutableList<String> labels = ImmutableList.of(Id.get("copy"));
    ArrayDeque<Command> result = new ArrayDeque<Command>();
    for (VariableDecl v : allWritten) {
      int wi = writeIdx.get(v).get(ca);
      int ri = readIdx.get(v).get(cb);
      if (ri == wi) continue;
      result.add(AssertAssumeCmd.mk(
          labels,
          AssertAssumeCmd.CmdType.ASSUME,
          ImmutableList.<Identifier>of(),
          BinaryOp.mk(
              BinaryOp.Op.EQ,
              AstUtils.mkId(name(v.name(), ri)),
              AstUtils.mkId(name(v.name(), wi))),
          ca.loc()));
      labels = noString;
    }
    return result;
  }

  private boolean isReturn(Command c) {
    if (!(c instanceof GotoCmd)) return false;
    GotoCmd gc = (GotoCmd) c;
    return gc.successors().isEmpty();
  }
}

