package freeboogie.vcgen;

import java.util.*;

import com.google.common.collect.*;
import genericutils.*;

import freeboogie.ast.*;
import freeboogie.tc.TcInterface;
import freeboogie.tc.TypeUtils;

/**
 * Havocs variables potentially assigned to in loops at the entry point
 * of the loop.
 */
public class HavocMaker extends CommandDesugarer {
  /* IMPLEMENTATION
   * 1. construct maps
   *      A: command -> scc
   *      B: entry point -> scc    (a submap of the above)
   *      C: scc -> set of vars potentially assigned to
   * 2. prepend havoc C(B(e)) to each entry point (while keeping
   *    the old labels (if any)
   *
   * The first step can be done with Kosaraju's algo for scc. If
   * we do the ordering with normal edges and the tagging with
   * reversed edges then, while we do the tagging we also see the
   * entry points as nodes from which you can reach (backwards)
   * nodes that are already in another scc.
   */
  private HashSet<Command> seen = Sets.newHashSet();
  private HashMap<Command, Integer> scc = Maps.newHashMap(); 
  private HashMap<Command, Integer> sccOfEntryPoint = Maps.newHashMap();
  private ArrayList<HashSet<String>> assignedVars = Lists.newArrayList();
  private ArrayList<Integer> sccSize = Lists.newArrayList();

  private int sccIndex; // the index of the scc being built
  private HashSet<String> sccAssignedVars; 
    // variables assigned in the scc being processed
  private ArrayList<Command> dfs2order = Lists.newArrayList();

  private SimpleGraph<Command> flowGraph;

  private ReadWriteSetFinder rw;

  private Block localNewBlock; // block possibly introduced by eval(Block...)

  @Override
  public Program process(Program ast, TcInterface tc) {
    this.tc = tc;
    rw = new ReadWriteSetFinder(tc.st());
    ast = (Program) ast.eval(this);
    return TypeUtils.internalTypecheck(ast, tc);
  }

  @Override public Implementation eval(Implementation implementation) {
    Body body = implementation.body();
    flowGraph = tc.flowGraph(implementation);
    seen.clear(); seen.add(null); dfs2order.clear();
    dfs1(body.block().commands().get(0));
    Collections.reverse(dfs2order);

    scc.clear(); sccOfEntryPoint.clear(); 
    assignedVars.clear(); sccSize.clear();
    sccIndex = -1;
    for (Command c : dfs2order) if (scc.get(c) == null) {
      sccSize.add(0);
      ++sccIndex;
      sccAssignedVars = Sets.newHashSet();
      assignedVars.add(sccAssignedVars);
      dfs2(c);
    }

    Body newBody = (Body) body.eval(this);
    if (newBody != body) {
      implementation = Implementation.mk(
          implementation.attributes(), 
          implementation.sig(), 
          newBody,
          implementation.loc());
    }
    return implementation;
  }

  @Override public AssignmentCmd eval(AssignmentCmd cmd) {
    if (entryPoint(cmd)) 
      cmd = AssignmentCmd.mk(noString, cmd.assignments(), cmd.loc());
    return cmd;
  }

  @Override public AssertAssumeCmd eval(AssertAssumeCmd cmd) {
    if (entryPoint(cmd)) {
      cmd = AssertAssumeCmd.mk(
          noString, 
          cmd.type(), 
          cmd.typeArgs(), 
          cmd.expr(), 
          cmd.loc());
    }
    return cmd;
  }

  @Override public void see(BreakCmd cmd) {
    assert false : "Break commands are assumed to be desugared at this stage.";
  }

  @Override public GotoCmd eval(GotoCmd cmd) {
    if (entryPoint(cmd))
      cmd = GotoCmd.mk(noString, cmd.successors(), cmd.loc());
    return cmd;
  }

  @Override public HavocCmd eval(HavocCmd cmd) {
    if (entryPoint(cmd))
      cmd = HavocCmd.mk(noString, cmd.ids(), cmd.loc());
    return cmd;
  }

  @Override public CallCmd eval(CallCmd cmd) {
    if (entryPoint(cmd)) {
      cmd = CallCmd.mk(
          noString, 
          cmd.procedure(), 
          cmd.types(), 
          cmd.results(), 
          cmd.args(), 
          cmd.loc());
    }
    return cmd;
  }

  private boolean entryPoint(Command c) {
    Integer cmdScc = sccOfEntryPoint.get(c);
    if (cmdScc != null 
        && sccSize.get(cmdScc) > 1 
        && !assignedVars.get(cmdScc).isEmpty()) {
      addEquivalentCommand(HavocCmd.mk(
          c.labels(),
          AstUtils.ids(assignedVars.get(cmdScc)), 
          c.loc()));
      return true;
    }
    return false;
  }

  // === scc ===

  private void dfs1(Command b) {
    if (seen.contains(b)) return;
    seen.add(b);
//System.out.println("dfs1 " + b.getName());
    for (Command c : flowGraph.to(b)) dfs1(c);
    dfs2order.add(b);
  }

  private void dfs2(Command b) {
    scc.put(b, sccIndex);
    sccSize.set(sccIndex, 1 + sccSize.get(sccIndex));
//System.out.println("dfs2 " + b.getName() + ", idx " + sccIndex);

    Pair<CSeq<VariableDecl>, CSeq<VariableDecl>> rwVars = b.eval(rw);
    for (VariableDecl vd : rwVars.second)
      sccAssignedVars.add(vd.name());

    for (Command c : flowGraph.from(b)) {
      Integer cScc = scc.get(c);
      if (cScc == null)
        dfs2(c);
      else if (cScc != sccIndex)
        sccOfEntryPoint.put(b, sccIndex);
    }
  }
}
