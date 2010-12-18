package freeboogie.vcgen;
// imports {{{1
import java.util.Map;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;

import freeboogie.ast.*;
// class LabelAdder {{{1
/** Adds labels to statements.
  For now, this is only used by {@code BreakDesugarer}, but may be useful
  elsewhere.
 */
public class LabelAdder extends Transformer {
  // interesting part {{{2
  private Map<Command, String> newLabels;

  public void newLabels(Map<Command, String> newLabels) {
    Preconditions.checkNotNull(newLabels);
    this.newLabels = newLabels;
  }

  private ImmutableList<String> newLabels(Command command) {
    String labelToAdd = newLabels.get(command);
    if (labelToAdd == null) return command.labels();
    return ImmutableList.<String>builder()
        .add(labelToAdd).addAll(command.labels()).build();
  }

  // forwarders {{{2
  @Override public AssertAssumeCmd eval(AssertAssumeCmd assertAssumeCmd) {
    return assertAssumeCmd.withLabels(newLabels(assertAssumeCmd));
  }
  @Override public AssignmentCmd eval(AssignmentCmd assignmentCmd) {
    return assignmentCmd.withLabels(newLabels(assignmentCmd));
  }
  @Override public BreakCmd eval(BreakCmd breakCmd) {
    return breakCmd.withLabels(newLabels(breakCmd));
  }
  @Override public CallCmd eval(CallCmd callCmd) {
    return callCmd.withLabels(newLabels(callCmd));
  }
  @Override public GotoCmd eval(GotoCmd gotoCmd) {
    return gotoCmd.withLabels(newLabels(gotoCmd));
  }
  @Override public HavocCmd eval(HavocCmd havocCmd) {
    return havocCmd.withLabels(newLabels(havocCmd));
  }
  @Override public IfCmd eval(IfCmd ifCmd) {
    return ifCmd.withLabels(newLabels(ifCmd));
  }
  @Override public WhileCmd eval(WhileCmd whileCmd) {
    return whileCmd.withLabels(newLabels(whileCmd));
  }
}
