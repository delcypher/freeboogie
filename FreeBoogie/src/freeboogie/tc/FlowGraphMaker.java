package freeboogie.tc;

import java.util.*;

import com.google.common.collect.*;
import genericutils.Err;
import genericutils.Pair;
import genericutils.SimpleGraph;

import freeboogie.ast.*;

/**
  Constructs a flowgraph of blocks for each implementation.

  After {@code process(ast)} you can ask {@code flowGraph(body)}
  to get a {@code SimpleGraph&lt;Command&gt;}.
  Processing throws {@code ErrorsFoundException} when there are
  undefined labels or multiply defined labels.
  Unreachability warnings are printed.

  @author rgrig
 */
public class FlowGraphMaker extends Transformer {
  /* IMPLEMENTATION NOTE

    For each type of command TC there is a function see(TC cmd)
    that adds the outgoing edges of cmd to the currentFlowGraph.
    To do so these functions need to know a little about their
    context. Blocks contain lists of commands, and there is
    no other place where commands occur. The top of the stack
    |nextCommand| always points the next command in the innermost
    such list, or |null| if the command being visited is the last
    one in the innermost such list. In turn, blocks appear only
    in `implementation bodies', `while' bodies, and `if' branches. A
    second stack, |enclosingScope|, keeps track of these. Note
    that |nextCommand.size()==enclosingScope.size()| whenever
    a command is visited.

    Since we iterate through these stacks (and we don't care
    only about the last element) they are implemented with
    ArrayList-s. (Other choices include (1) ArrayDeque, which is
    faster, and an Iterator for traversal, which is slower, or
    (2) a singly linked list).

    When a non-branching command is being visited we find the
    next command by searching for the first nonnull element
    of |nextCommand| (starting from the top, which is where
    you pop).

    Dealing with |break| is only a bit more complicated. The first
    step is to identify the while/if command it refers to. We do so
    by traveling the |enclosingScope| stack until we find the
    first while command that has a matching label.

    The second step works like this:
      connect(break, lastCmd, lastScope)
        if nextCommand[lastCmd] != null
          edge(break, nextCommand[lastCmd])
        else
          switch (typeof(enclosingScope[lastScope]))
            case Body: do nothing
            case WhileCmd: edge(break, enclosingScope[lastScope])
            case IfCmd: connect(break, lastCmd-1, lastScope-1)
    In words: If we are last in a list of statements then that
    list of statements comes either from an implementation (in
    which case 'break' means 'return'), a while command (in which
    case we go to the while command), or an if command (in which
    case we act as if we were requested to break out of that if
    command).

    In order to process goto commands we first use
    |LabelsCollector| to link labels to their commands.
   */

  // The two stacks described in the implementation note above.
  private ArrayList<Command> nextCommand = Lists.newArrayList();
  private ArrayList<Ast> enclosingScope = Lists.newArrayList();

  // TODO(radugrigore): Should this be handed over from the client?
  // Used for handling goto (but *not* for handling break).
  private LabelsCollector labelsCollector;

  // Used for querying |labelsCollector|.
  private Implementation currentImplementation;

  // the flow graph currently being built
  private SimpleGraph<Command> currentFlowGraph;

  // maps implementations to their flowgraphs
  private HashMap<Implementation, SimpleGraph<Command>> flowGraphs;

  // the detected problems
  private List<FbError> errors;
  private List<FbError> warnings = Lists.newArrayList();

  // used for reachability (DFS)
  private HashSet<Command> seenCommands = Sets.newHashSet();

  // used to break out of loops
  private ArrayDeque<WhileCmd> whileStack = new ArrayDeque<WhileCmd>();

  // === public interface ===

  /** Constructs flow graphs for {@code ast}.
      It also prints warnings if there are syntactically unreachable blocks. */
  public Program process(Program ast)
  throws ErrorsFoundException {
    nextCommand.clear();
    enclosingScope.clear();
    warnings.clear();
    labelsCollector = new LabelsCollector();
    errors = Lists.newArrayList();
    flowGraphs = Maps.newHashMap();
    labelsCollector.process(ast);
    ast.eval(this);   // build the graph
    FbError.reportAll(warnings);
    for (SimpleGraph<Command> fg : flowGraphs.values())
      fg.freeze();
    if (!errors.isEmpty()) throw new ErrorsFoundException(errors);
    return ast;
  }


  /** Returns the command flow graph for {@code body}. */
  public SimpleGraph<Command> flowGraph(Implementation implementation) {
    return flowGraphs.get(implementation);
  }

  public LabelsCollector labels() {
    return labelsCollector;
  }

  // === helpers ===

  private void dfs(Command c) {
    if (seenCommands.contains(c)) return;
    seenCommands.add(c);
    Set<Command> children = currentFlowGraph.to(c);
    for (Command d : children) dfs(d);
  }

  // BEGIN top-level methods {{{
  @Override public void see(Implementation implementation) {
    // build graph
    currentFlowGraph = new SimpleGraph<Command>();
    flowGraphs.put(implementation, currentFlowGraph);
    currentImplementation = implementation;
    implementation.body().eval(this);

    // check reachability
    // XXX check
    seenCommands.clear();
    ImmutableList<Command> commands = implementation.body().block().commands();
    if (commands.isEmpty()) return;
    dfs(commands.get(0));
    for (Command c : labelsCollector.allCommands(implementation)) {
      if (!seenCommands.contains(c))
        warnings.add(new FbError(FbError.Type.UNREACHABLE, c, rep(c)));
    }
  }

  @Override public void see(Body body) {
    enclosingScope.add(body);
    body.block().eval(this);
    enclosingScope.remove(enclosingScope.size() - 1);
  }

  @Override public void see(Block block) {
    ImmutableList<Command> commands = block.commands();
    for (int i = 1; i < commands.size(); ++i) {
      nextCommand.add(commands.get(i));
      commands.get(i-1).eval(this);
      nextCommand.remove(nextCommand.size() - 1);
    }
    if (!commands.isEmpty()) {
      nextCommand.add(null);
      commands.get(commands.size() - 1).eval(this);
      nextCommand.remove(nextCommand.size() - 1);
    }
  }

  private String rep(Command c) {
    if (c.labels().isEmpty()) return "";
    StringBuilder sb = new StringBuilder();
    sb.append("(");
    for (int i = 0; i < c.labels().size(); ++i) {
      if (i != 0) sb.append(", ");
      sb.append(c.labels().get(i));
    }
    sb.append(")");
    return sb.toString();
  }
  // END top-level methods }}}

  // BEGIN visit nonbranching commands {{{
  private void processNonbranchingCommand(Command command) {
    assert nextCommand.size() == enclosingScope.size() : "see impl note";
    currentFlowGraph.node(command);
    int i = nextCommand.size();
    while (--i >= 0) {
      if (nextCommand.get(i) != null) {
        currentFlowGraph.edge(command, nextCommand.get(i));
        return;
      } else if (enclosingScope.get(i) instanceof WhileCmd) {
        currentFlowGraph.edge(command, (Command) enclosingScope.get(i));
        return;
      }
    }
  }

  @Override public void see(AssertAssumeCmd assertAssumeCmd) {
    processNonbranchingCommand(assertAssumeCmd);
  }

  @Override public void see(AssignmentCmd assignmentCmd) {
    processNonbranchingCommand(assignmentCmd);
  }

  @Override public void see(CallCmd callCmd) {
    processNonbranchingCommand(callCmd);
  }

  @Override public void see(HavocCmd havocCmd) {
    processNonbranchingCommand(havocCmd);
  }
  // END visit nonbranching commands }}}

  // BEGIN visit branching commands {{{
  @Override public void see(IfCmd ifCmd) {
    currentFlowGraph.node(ifCmd);
    if (!ifCmd.yes().commands().isEmpty()) {
      currentFlowGraph.edge(ifCmd, ifCmd.yes().commands().get(0));
      enclosingScope.add(ifCmd);
      ifCmd.yes().eval(this);
      enclosingScope.remove(enclosingScope.size() - 1);
    }
    if (ifCmd.no() != null && !ifCmd.no().commands().isEmpty()) {
      currentFlowGraph.edge(ifCmd, ifCmd.no().commands().get(0));
      enclosingScope.add(ifCmd);
      ifCmd.no().eval(this);
      enclosingScope.remove(enclosingScope.size() - 1);
    } else processNonbranchingCommand(ifCmd);
  }

  @Override public void see(WhileCmd whileCmd) {
    currentFlowGraph.node(whileCmd);
    processNonbranchingCommand(whileCmd);
    ImmutableList<Command> commands = whileCmd.body().commands();
    if (!commands.isEmpty())
      currentFlowGraph.edge(whileCmd, commands.get(0));
    enclosingScope.add(whileCmd);
    whileCmd.body().eval(this);
    enclosingScope.remove(enclosingScope.size() - 1);
  }

  @Override public void see(GotoCmd gotoCmd) {
    currentFlowGraph.node(gotoCmd);
    for (String s : gotoCmd.successors()) {
      Command next = labelsCollector.command(currentImplementation, s);
      if (next == null)
        errors.add(new FbError(FbError.Type.MISSING_BLOCK, gotoCmd, s));
      else
        currentFlowGraph.edge(gotoCmd, next);
    }
  }

  // See the implementation note at the beginning of the class.
  @Override public void see(BreakCmd breakCmd) {
    assert nextCommand.size() == enclosingScope.size() : "see impl note";
    currentFlowGraph.node(breakCmd);
    String l = breakCmd.successor();

    // Find the target of break.
    int i = nextCommand.size();
    while (--i > 0) {
      Ast target = enclosingScope.get(i);
      if (target instanceof WhileCmd) {
        WhileCmd t = (WhileCmd) target;
        if (l == null || t.labels().indexOf(l) != -1) break;
      } else {
        assert target instanceof IfCmd;
        IfCmd t = (IfCmd) target;
        if (t.labels().indexOf(l) != -1) break;
      }
    }

    // Find what follows the target.
    if (i == 0)
      errors.add(new FbError(FbError.Type.BAD_BREAK_TARGET, breakCmd));
    else while (--i >= 0) {
      Command c = nextCommand.get(i);
      Ast s = enclosingScope.get(i);
      if (c != null) {
        currentFlowGraph.edge(breakCmd, c);
        break;
      } else if (s instanceof WhileCmd) {
        currentFlowGraph.edge(breakCmd, (Command) s);
        break;
      }
    }
  }
  // END visit branching commands }}}
}
