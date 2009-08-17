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
public class HavocMaker extends Transformer {
  /* IMPLEMENTATION
   * 1. construct maps
   *      A: block -> scc
   *      B: entry point -> scc    (a submap of the above)
   *      C: scc -> set of vars potentially assigned to
   * 2. replace each entry point e by
   *      havoc C(B(e)); goto old_e
   *
   * The first step can be done with Kosaraju's algo for scc. If
   * we do the ordering with normal edges and the tagging with
   * reversed edges then, while we do the tagging we also see the
   * entry points as nodes from which you can reach (backwards)
   * nodes that are already in another scc.
   */
  private HashSet<Block> seen = Sets.newHashSet();
  private HashMap<Block, Integer> scc = Maps.newHashMap(); 
  private HashMap<Block, Integer> sccOfEntryPoint = Maps.newHashMap();
  private ArrayList<HashSet<String>> assignedVars = Lists.newArrayList();
  private ArrayList<Integer> sccSize = Lists.newArrayList();

  private int sccIndex; // the index of the scc being built
  private HashSet<String> sccAssignedVars; 
    // variables assigned in the scc being processed
  private ArrayList<Block> dfs2order = Lists.newArrayList();

  private SimpleGraph<Block> flowGraph;

  private ReadWriteSetFinder rw;

  private Block localNewBlock; // block possibly introduced by eval(Blocck...)

  @Override
  public Program process(Program ast, TcInterface tc) {
    this.tc = tc;
    rw = new ReadWriteSetFinder(tc.st());
    ast = (Program) ast.eval(this);
    return TypeUtils.internalTypecheck(ast, tc);
  }

  @Override
  public Implementation eval(
    Implementation implementation,
    ImmutableList<Attribute> attr,
    Signature sig,
    Body body
  ) {
    flowGraph = tc.flowGraph(implementation);
    seen.clear(); seen.add(null); dfs2order.clear();
    dfs1(body.blocks().get(0));
    Collections.reverse(dfs2order);

    scc.clear(); sccOfEntryPoint.clear(); 
    assignedVars.clear(); sccSize.clear();
    sccIndex = -1;
    for (Block b : dfs2order) if (scc.get(b) == null) {
      sccSize.add(0);
      ++sccIndex;
      sccAssignedVars = new HashSet<String>();
      assignedVars.add(sccAssignedVars);
      dfs2(b);
    }

    Body newBody = (Body) body.eval(this);
    if (newBody != body)
      implementation = Implementation.mk(attr, sig, newBody);
    return implementation;
  }

  @Override public Body eval(
      Body body, 
      ImmutableList<VariableDecl> vars,
      ImmutableList<Block> blocks
  ) {
    boolean same = true;
    ImmutableList.Builder<Block> newBlocks = ImmutableList.builder();
    for (Block b : blocks) {
      localNewBlock = null;
      Block nb = (Block) b.eval(this);
      same &= localNewBlock == null && nb == b;
      if (localNewBlock != null) newBlocks.add(localNewBlock);
      newBlocks.add(nb);
    }
    if (!same) body = Body.mk(vars, newBlocks.build());
    return body;
  }

  @Override
  public Block eval(
      Block block, 
      String name, 
      Command cmd, 
      ImmutableList<AtomId> succ
  ) {
    Integer blockScc = sccOfEntryPoint.get(block);
//System.out.println("process " + name);
    if (blockScc != null 
        && sccSize.get(blockScc) > 1 
        && !assignedVars.get(blockScc).isEmpty()) {
//System.out.println("change " + name);
      String tmpName = Id.get("loop_entry");
      block = Block.mk(tmpName, cmd, succ);
      localNewBlock = Block.mk(
        name,
        HavocCmd.mk(idsFromStrings(assignedVars.get(blockScc))),
        AstUtils.ids(tmpName));
    }
    return block;
  }

  // === scc ===

  private void dfs1(Block b) {
    if (seen.contains(b)) return;
    seen.add(b);
//System.out.println("dfs1 " + b.getName());
    for (Block c : flowGraph.to(b)) dfs1(c);
    dfs2order.add(b);
  }

  private void dfs2(Block b) {
    scc.put(b, sccIndex);
    sccSize.set(sccIndex, 1 + sccSize.get(sccIndex));
//System.out.println("dfs2 " + b.getName() + ", idx " + sccIndex);

    Command cmd = b.cmd();
    if (cmd != null) {
      Pair<CSeq<VariableDecl>, CSeq<VariableDecl>> rwVars = cmd.eval(rw);
      for (VariableDecl vd : rwVars.second)
        sccAssignedVars.add(vd.name());
    }

    for (Block c : flowGraph.from(b)) {
      Integer cScc = scc.get(c);
      if (cScc == null)
        dfs2(c);
      else if (cScc != sccIndex)
        sccOfEntryPoint.put(b, sccIndex);
    }
  }

  // === helpers ===

  private ImmutableList<AtomId> idsFromStrings(Iterable<String> sl) {
    ImmutableList.Builder<AtomId> b = ImmutableList.builder();
    for (String s : sl) b.add(AtomId.mk(s, null));
    return b.build();
  }
}
