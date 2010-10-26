package freeboogie.vcgen;

import java.util.HashSet;
import java.util.Set;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Sets;
import genericutils.Err;
import genericutils.Pair;
import genericutils.SimpleGraph;

import freeboogie.ast.*;

/**
 * Cuts back edges and removes unreachable commands. (Back edges
 * according to some arbitrary DFS.)
 */
public class LoopCutter extends CommandDesugarer {
  private SimpleGraph<Command> currentFG;

  private HashSet<Command> seen = Sets.newHashSet();
  private HashSet<Command> done = Sets.newHashSet();
  private HashSet<Pair<Command, Command>> toRemove = Sets.newHashSet();
  private boolean hasStuck;

  // === transformer methods ===

  @Override public Body eval(Body body) {
    Block block = body.block();
    seen.clear();
    done.clear();
    toRemove.clear();
    currentFG = tc.flowGraph(body);
    dfs(block.commands().get(0));
    block = (Block) block.eval(this);
    return Body.mk(body.vars(), block, body.loc());
  }

  @Override public void see(BreakCmd breakCmd) {
    assert false : "Break commands are assumed to be desugared at this stage.";
  }

  @Override public Command eval(GotoCmd command) {
    if (!done.contains(command)) return null;
    ImmutableList.Builder<String> builder = ImmutableList.builder();
    for (Command c : currentFG.to(command)) {
      if (!toRemove.contains(Pair.of(command, c))) 
        builder.add(c.labels().get(0));
    }
    ImmutableList<String> newSuccessors = builder.build();
    if (newSuccessors.isEmpty() && !command.successors().isEmpty())
      addEquivalentCommand(AstUtils.stuckCmd(command.labels(), command.loc()));
    return GotoCmd.mk(command.labels(), newSuccessors, command.loc());
  }

  @Override public Command eval(AssertAssumeCmd assertAssumeCmd) {
    return processCommand(assertAssumeCmd);
  }

  @Override public Command eval(AssignmentCmd assignmentCmd) {
    return processCommand(assignmentCmd);
  }

  @Override public Command eval(CallCmd callCmd) {
    return processCommand(callCmd);
  }

  @Override public Command eval(HavocCmd havocCmd) {
    return processCommand(havocCmd);
  }

  private Command processCommand(Command command) {
    if (!done.contains(command)) return null;
    Set<Command> next = currentFG.to(command);
    assert next.size() == 1;
    if (toRemove.contains(Pair.of(command, next.iterator().next()))) {
      addEquivalentCommand(command);
      return GotoCmd.mk(noString, noString, command.loc());
    }
    return command;
  }

  @Override public void see(WhileCmd whileCmd) {
    Err.internal("While commands should have been desugared.");
  }

  // === depth first search for back edges ===

  private void dfs(Command b) {
    seen.add(b);
    for (Command c : currentFG.to(b)) {
      if (done.contains(c)) continue;
      if (seen.contains(c))
        toRemove.add(Pair.of(b, c));
      else
        dfs(c);
    }
    done.add(b);
  }
}
