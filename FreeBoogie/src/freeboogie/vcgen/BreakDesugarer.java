package freeboogie.vcgen;
// imports {{{1
import java.util.Map;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Maps;
import genericutils.Id;
import genericutils.SimpleGraph;

import freeboogie.ast.*;

// BreakDesugarer {{{1
/** Desugars <b>break</b> statements.
  
  Each <b>break</b> command is equivalent to a <b>goto</b>
  command whose targets are given by the flowgraph. This
  transformer may introduce extra labels.
 */
public class BreakDesugarer extends Transformer {
  // fields {{{2
  private LabelAdder labelAdder = new LabelAdder();
  private Map<Command, String> newLabel = Maps.newHashMap();
  private SimpleGraph<Command> flowgraph;

  // the interesting part {{{2
  private String label(Command command) {
    String label = tc.labels().someLabel(command);
    if (label == null) label = newLabel.get(command);
    if (label == null) {
      label = Id.get("break");
      newLabel.put(command, label);
    }
    return label;
  }

  @Override public Program eval(Program program) {
    return program.withImplementations(
        AstUtils.evalListOfImplementation(program.implementations(), this));
  }

  @Override public Implementation eval(Implementation implementation) {
    newLabel.clear();
    flowgraph = tc.flowGraph(implementation);
    Body newBody = AstUtils.eval(implementation.body(), this);
    labelAdder.newLabels(newLabel);
    return implementation.withBody(AstUtils.eval(newBody, labelAdder));
  }

  @Override public GotoCmd eval(BreakCmd command) {
    ImmutableList.Builder<String> successors = ImmutableList.builder();
    for (Command c : flowgraph.to(command))
      successors.add(label(c));
    return GotoCmd.mk(command.labels(), successors.build(), command.loc());
  }
}
