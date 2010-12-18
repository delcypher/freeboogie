package astgen;

import java.io.*;
import java.util.*;
import java.util.logging.Logger;

import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import genericutils.Err;

/**
 * The template parser. This is where the output is produced. By
 * default the output is set to {@code null} which means that
 * the beginning of a template can contain arbitrary comments.
 * The <tt>\file</tt> macro switches the output to another
 * destination. (A common trick is to use /dev/stdout as a
 * sink to inform the user about the progress of the template
 * processing.) The method {@code setOutputPath} can be used to 
 * determine the output directory.
 *
 * Some macros must be nested in others. For example
 * \class_name must be nested in \classes or \normal_classes or
 * \abstract_classes. If the nesting is incorrect a warning is
 * printed on the console and &lt;WRONG_MACRO&gt; goes to the
 * output. If there are nested \classes macros then only the
 * innermost one is considered. (In most applications nested list
 * macros should not be needed.)
 *
 * See test/nested_members to see why context stacks are useful.
 * 
 * TODO: consider adding an optional parameter for macros that indicates
 *       a nesting level such that, for example, the following is legal
 *          \classes{(\classes{\ClassName[0],\ClassName[1]})}
 *       and prints all pairs of class names.
 * 
 * TODO The duplicated code is a bit too much for my taste.
 * 
 * @author rgrig 
 * @author Mikolas Janota 
 */
public class TemplateParser {
  /*
   * The function |processTop| is the main loop. It reads a
   * token and distributes the work to various |process*| methods.
   * It is also responsible for stopping when a certain closing
   * } or ] is met (and it reads it). The variables |curlyCnt|
   * and |bracketCnt| count the nesting (since the beginning
   * of the template) and are used to identify on which ] or }
   * we should stop. Notice that the user shouldn't use unbalanaced
   * paranthesis in the template for this scheme to work.
   * 
   * The stacks |*Context| contain information about the nested
   * macros seen in the input.
   */

  @SuppressWarnings("serial")
  private static class EofReached extends IOException {}

  private static final Logger log = Logger.getLogger("astgen");
  
  private TemplateLexer lexer;
  private Grammar grammar;
  
  private Stack<AgClass> classContext;
  private Stack<AgMember> memberContext;
  private Stack<AgEnum> enumContext;
  private Stack<String> valueContext;
  private Stack<String> invariantContext;
  
  private Writer output;
  private String outputPath = null; // output directory 

  private int curlyCnt; // counts {} nesting
  private int bracketCnt; // counts [] nesting
  
  private TemplateToken lastToken;
  
  private boolean balancedWarning = true;

  // classes are processed in alphabetical order
  private Set<AgClass> orderedClasses;
  private Set<AgClass> abstractClasses;
  private Set<AgClass> normalClasses;
  
  /**
   * Prepares for parsing a template.
   *
   * @param fileName the name of the template file
   * @throws FileNotFoundException if the template file is not found
   */
  public TemplateParser(String fileName) throws FileNotFoundException {
    FileInputStream fis = new FileInputStream(fileName);
    CharStream cs = new CharStream(fis, fileName);
    lexer = new TemplateLexer(cs);
    output = null;
    lastToken = null;
    
    classContext = new Stack<AgClass>();
    memberContext = new Stack<AgMember>();
    enumContext = new Stack<AgEnum>();
    valueContext = new Stack<String>();
    invariantContext = new Stack<String>();

    orderedClasses = null;
    abstractClasses = null;
    normalClasses = null;
  }

  /** Set the directory where the output files should be generated,
   *  if null, then goes to current. */
  //@modifies outputPath; 
  public void setOutputPath(/*@nullable*/String path) {
    outputPath = path;
  }


  /**
   * Processes the current template using grammar {@code g}.
   * @param g the grammar
   * @throws IOException 
   */
  public void process(Grammar g) throws IOException {
    grammar = g;
    for (Map.Entry<String, String> e : g.userDefs.entrySet()) {
      List<TemplateToken> equiv = Lists.newArrayList();
      equiv.add(new TemplateToken(
          TemplateToken.Type.OTHER, 
          e.getValue(),
          TemplateToken.Case.ORIGINAL_CASE));
      lexer.addShorthand("\\" + e.getKey(), equiv);
    }
    processTop(Integer.MAX_VALUE, Integer.MAX_VALUE);
    if (output != null) output.flush();
  }

  /*
   * For now I will enforce {} and [] to be balanced pretty much 
   * everywhere.
   * 
   * The function dispatches the work to the appropriate worker.
   * It also takes care of stoping when a } or a ] with a given
   * nesting level is seen.
   */
  private void processTop(int curlyStop, int bracketStop) throws IOException {
    try {
      readToken();
      while (true) {
        switch (lastToken.type) {
        case FILE:
          processFile(); break;
        case CLASSES:
          processClasses(); break;
        case IF_ABSTRACT:
          processIsAbstract(); break;
        case ABSTRACT_CLASSES:
          processAbstractClasses(); break;
        case NORMAL_CLASSES:
          processNormalClasses(); break;
        case CLASS_NAME:
          processClassName(); break;
        case BASE_NAME:
          processBaseName(); break;
        case MEMBERS:
          processMembers(); break;
        case SELFMEMBERS:
          processSelfMembers(); break;
        case INHERITEDMEMBERS:
          processInheritedMembers(); break;
        case MEMBER_TYPE:
          processMemberType(); break;
        case MEMBER_NAME:
          processMemberName(); break;
        case IF_PRIMITIVE:
          processIfPrimitive(); break;
        case IF_NONNULL:
          processIfNonnull(); break;
        case IF_ENUM:
          processIfEnum(); break;
        case IF_TAGGED:
          processIfTagged(); break;
        case IF_TERMINAL:
          processIfTerminal(); break;
        case CHILDREN:
          processChildren(); break;
        case PRIMITIVES:
          processPrimitives(); break;
        case ENUMS:
          processEnums(); break;
        case ENUM_NAME:
          processEnumName(); break;
        case VALUES:
          processValues(); break;
        case VALUE_NAME:
          processValueName(); break;
        case INVARIANTS:
          processInvariants(); break;
        case INV:
          processInv(); break;
        case DEF:
          processDef(); break;
        default:
          if (curlyStop == curlyCnt || bracketStop == bracketCnt) return;
          write(lastToken.rep());
        }
        if (curlyCnt == 0 && bracketCnt == 0) lexer.unmark();
        readToken();
      }
    } catch (EofReached e) { /* fine */ }
  }
  
  /*
   * Reads { file_name } and makes output point to file_name.
   * If the file cannot be open then switch to a null output
   * and give a warning.
   */
  private void processFile() throws IOException {
    readToken();
    if (lastToken.type != TemplateToken.Type.LC) {
      err("Hey, \\file should be followed by {");
      Err.help("I'm gonna stop producing output.");
      switchOutput(null);
      skipToRc(curlyCnt, true);
      return;
    }
    StringWriter sw = new StringWriter();
    switchOutput(sw);
    processTop(curlyCnt - 1, Integer.MAX_VALUE);
    String fn = sw.toString().replaceAll("\\s+", "_");
    try {
      File f = outputPath==null ? new File(fn) : new File(outputPath, fn);
      FileWriter fw = new FileWriter(f);
      switchOutput(fw);
      log.info("The output goes to the file " + fn);
    } catch (IOException e) {
      err("Cannot write to file " + fn);
      Err.help("I'm gonna stop producing output.");
      switchOutput(null);
    }
  }

  /** Reads the separator that will separate the members of {@code set}, 
   *  which are communicated via {@code stack}. 
   */
  private <T> void processList(Collection<T> set, Stack<T> stack)
  throws IOException {
    readToken();
    String separator = "";
    if (lastToken.type == TemplateToken.Type.LB) {
      readToken();
      if (lastToken.type != TemplateToken.Type.OTHER) {
          err("Sorry, you can't use any funny stuff as a separator.");
        skipToRc(curlyCnt, true);
        return;
      }
      separator = lastToken.rep();
      readToken();
      if (lastToken.type != TemplateToken.Type.RB) {
        err("The separator is not properly closed by ].");
        skipToRb(bracketCnt - 1, true);
      }
      if (lastToken.type != TemplateToken.Type.LC)
        readToken();
    }
    if (lastToken.type != TemplateToken.Type.LC) {
      err("There should be a { after a list macro.");
      skipToRc(curlyCnt - 1, true);
      return;
    }
    if (set.isEmpty()) skipToRc(curlyCnt - 1, false);
    int i = 0; // TODO is there another way to check if I'm looking at the last?
    for (T el : set) {
      if (i != 0) {
        lexer.rewind();
        write(separator);
        ++curlyCnt;
      }
      if (++i != set.size()) lexer.mark();
        
      stack.add(el);
      processTop(curlyCnt - 1, Integer.MAX_VALUE);
      stack.pop();
    }
  }
  
  private void processClasses() throws IOException {
    splitClasses();
    processList(orderedClasses, classContext);
  }
  
  private void processYesNo(boolean yes) throws IOException {
    if (!yes) skipToRc(curlyCnt, false);
    eat(TemplateToken.Type.LC);
    processTop(curlyCnt - 1, Integer.MAX_VALUE);
    if (yes) skipToRc(curlyCnt, false);
  }
  
  private void processIsAbstract() throws IOException {
    if (!checkContext(classContext)) {
      skipToRc(curlyCnt, true);
      skipToRc(curlyCnt, true);
      return;
    }
    processYesNo(classContext.peek().getMembers().isEmpty());
  }
  
  private void splitClasses() {
    if (abstractClasses != null) return;
    orderedClasses = new TreeSet<AgClass>();
    abstractClasses = new TreeSet<AgClass>();
    normalClasses = new TreeSet<AgClass>();
    for (AgClass c: grammar.classes.values()) {
      orderedClasses.add(c);
      if (c.getMembers().isEmpty())
        abstractClasses.add(c);
      else
        normalClasses.add(c);
    }
  }
  
  private void processAbstractClasses() throws IOException {
    splitClasses();
    processList(abstractClasses, classContext);
  }
  
  private void processNormalClasses() throws IOException {
    splitClasses();
    processList(normalClasses, classContext);
  }
  
  private <T> boolean checkContext(Stack<T> context) throws IOException {
    if (context.isEmpty()) {
      err("Macro used in a wrong context.");
      write("<WRONG_MACRO>");
      return false;
    }
    return true;
  }
  
  private void processClassName() throws IOException {
    if (checkContext(classContext)) 
      writeId(classContext.peek().name, lastToken.idCase);
  }
  
  private void processBaseName() throws IOException {
    if (checkContext(classContext))  
      writeId(classContext.peek().getBaseClassName(), lastToken.idCase);
  }
  
  private void processMembers() throws IOException {
    if (!checkContext(classContext)) {
      skipToRc(curlyCnt, true);
      return;
    }
    processList(classContext.peek().getMembers(), memberContext);
  }

  private void processSelfMembers() throws IOException {
    if (!checkContext(classContext)) {
      skipToRc(curlyCnt, true);
      return;
    }
    processList(classContext.peek().getSelfMembers(), memberContext);
  }

  private void processInheritedMembers() throws IOException {
    if (!checkContext(classContext)) {
      skipToRc(curlyCnt, true);
      return;
    }
    processList(classContext.peek().getInheritedMembers(), memberContext);
  }

  
  private void processMemberType() throws IOException {
    if (checkContext(memberContext))
      writeId(memberContext.peek().type, lastToken.idCase);
  }
  
  private void processMemberName() throws IOException {
    if (checkContext(memberContext))
      writeId(memberContext.peek().name, lastToken.idCase);
  }
  
  private void processIfPrimitive() throws IOException {
    if (!checkContext(memberContext)) {
      skipToRc(curlyCnt, true);
      skipToRc(curlyCnt, true);
      return;
    }
    processYesNo(memberContext.peek().primitive);
  }
  
  private void processIfNonnull() throws IOException {
    if (!checkContext(memberContext)) {
      skipToRc(curlyCnt, true);
      skipToRc(curlyCnt, true);
      return;
    }
    processYesNo(memberContext.peek().tags.contains("nonnull"));
  }
  
  private void processIfEnum() throws IOException {
    if (!checkContext(memberContext)) {
      skipToRc(curlyCnt, true);
      skipToRc(curlyCnt, true);
      return;
    }
    processYesNo(memberContext.peek().isenum);
  }

  private void processIfTagged() throws IOException {
    if (!checkContext(memberContext)) {
      skipToRc(curlyCnt, true);
      skipToRc(curlyCnt, true);
      skipToRc(curlyCnt, true);
      return;
    }
    readToken();
    if (lastToken.type != TemplateToken.Type.LC) {
      err("You should give a { tag expression } after \\if_tagged.");
      Err.help("I'll act as if <" + lastToken.rep() + "> was {.");
    }
    processYesNo(evalTagExpr(memberContext.peek().tags));
  }

  private void processIfTerminal() throws IOException {
    if (!checkContext(classContext)) {
      skipToRc(curlyCnt, true);
      skipToRc(curlyCnt, true);
      return;
    }
    processYesNo(classContext.peek().isTerminal());
  }


  private void processChildren() throws IOException {
    if (!checkContext(classContext)) {
      skipToRc(curlyCnt, true);
      return;
    }
    List<AgMember> children = new ArrayList<AgMember>(23);
    for (AgMember m : classContext.peek().getMembers())
      if (!m.primitive) children.add(m);
    processList(children, memberContext);
  }
  
  private void processPrimitives() throws IOException {
    if (!checkContext(classContext)) {
      skipToRc(curlyCnt, true);
      return;
    }
    List<AgMember> primitives = new ArrayList<AgMember>(23);
    for (AgMember m : classContext.peek().getMembers())
      if (m.primitive) primitives.add(m);
    processList(primitives, memberContext);
  }
  
  private void processEnums() throws IOException {
    if (!checkContext(classContext)) {
      skipToRc(curlyCnt, true);
      return;
    }
    processList(classContext.peek().enums, enumContext);
  }
  
  private void processEnumName() throws IOException {
    if (checkContext(enumContext))
      writeId(enumContext.peek().name, lastToken.idCase);
  }
  
  private void processValues() throws IOException {
    if (!checkContext(enumContext)) {
      skipToRc(curlyCnt, true);
      return;
    }
    processList(enumContext.peek().values, valueContext);
  }
  
  private void processValueName() throws IOException {
    if (checkContext(valueContext))
      writeId(valueContext.peek(), lastToken.idCase);
  }
  
  private void processInvariants() throws IOException {
    if (!checkContext(classContext)) {
      skipToRc(curlyCnt, true);
      return;
    }
    processList(classContext.peek().invariants, invariantContext);
  }
  
  private void processInv() throws IOException {
    if (checkContext(invariantContext))
      write(invariantContext.peek());
  }

  private void processDef() throws IOException {
    eat(TemplateToken.Type.LC);
    readToken();
    if (lastToken.type != TemplateToken.Type.OTHER) {
      err("You can't use funny stuff as the name of a user shorthand.");
      skipToRc(curlyCnt, true);
      skipToRc(curlyCnt, true);
      return;
    }
    String shorthand = "\\" + lastToken.rep().trim();
    eat(TemplateToken.Type.RC);
    int exitLevel = curlyCnt;
    eat(TemplateToken.Type.LC);
    List<TemplateToken> def = Lists.newArrayList();
    while (true) {
      readRawToken();
      if (lastToken.type == TemplateToken.Type.RC && curlyCnt == exitLevel)
        break;
      def.add(lastToken);
    }
    lexer.addShorthand(shorthand, def);
  }

  private boolean evalTagExpr(Set<String> tags) throws IOException {
    boolean value = evalTagAtom(tags);
    while (true) {
      readToken();
      TemplateToken.Type op = lastToken.type;
      switch (op) {
        case RP:
        case RC:
          return value;
      }
      boolean v = evalTagAtom(tags);
      switch (op) {
        case AND: value &= v; break;
        case OR: value |= v; break;
        default:
          err("Tag expressions can only contain ( ) | & and identifiers.");
      }
    }
  }

  private boolean evalTagAtom(Set<String> tags) throws IOException {
    readToken();
    if (lastToken.type == TemplateToken.Type.LP)
      return evalTagExpr(tags);
    else if (lastToken.type == TemplateToken.Type.OTHER)
      return tags.contains(lastToken.rep().trim());
    else {
      err("I was expecting a tag here.");
      return false;
    }
  }
  
  private void skipToRc(int cnt, boolean warn) throws IOException {
    skipToR(cnt, Integer.MAX_VALUE, warn);
  }
  
  private void skipToRb(int cnt, boolean warn) throws IOException {
    skipToR(Integer.MAX_VALUE, cnt, warn);
  }
  
  /*
   * This reads the input until either it finishes or the } or ]
   * with the specified nesting level is encountered. 
   */
  private void skipToR(int curlyStop, int bracketStop, boolean w)
  throws IOException {
    StringBuilder sb = new StringBuilder();
    while (true) {
      readToken();
      if (lastToken == null) break;
      sb.append(lastToken.rep());
      if (lastToken.type == TemplateToken.Type.RC 
        && curlyStop == curlyCnt) break;
      if (lastToken.type == TemplateToken.Type.RB 
        && bracketStop == bracketCnt) break;
    } 
    if (w) Err.help("I'm skipping: " + sb);
  }

  private TemplateToken reallyGetToken(boolean expand) throws IOException {
    TemplateToken r = lexer.next(expand);
    if (r == null) throw new EofReached();
    return r;
  }

  private void eat(TemplateToken.Type expected) throws IOException {
    readTokenGeneric(expected, true);
  }

  private void readToken() throws IOException {
    readTokenGeneric(null, true);
  }

  private void readRawToken() throws IOException {
    readTokenGeneric(null, false);
  }

  private void readTokenGeneric(TemplateToken.Type expected, boolean expand)
  throws IOException {
    lastToken = reallyGetToken(expand);
    log.finer("read token <" + lastToken.rep() + "> of type " + lastToken.type);
    if (expected != null) {
      if (expected != lastToken.type) {
        err("I was expecting " + expected.name() + ".");
        Err.help("I'll act as if <" + lastToken.rep() + "> is a " + 
            expected.name() + ".");
      }
      lastToken.type = expected;
    }
    if (lastToken.type == TemplateToken.Type.LB) ++bracketCnt;
    if (lastToken.type == TemplateToken.Type.RB) --bracketCnt;
    if (lastToken.type == TemplateToken.Type.LC) ++curlyCnt;
    if (lastToken.type == TemplateToken.Type.RC) --curlyCnt;
    if (balancedWarning && (curlyCnt < 0 || bracketCnt < 0)) {
      err("You are on thin ice.");
      Err.help("I don't guarantee what happens if you use unbalaced [] or {}.");
      balancedWarning = false;
    }
  }

  private void switchOutput(Writer newOutput) throws IOException {
    if (output != null) output.flush();
    output = newOutput;
    if (output == null) 
      log.fine("Output is turned off.");
  }

  private void writeId(String id, TemplateToken.Case cs) throws IOException {
    write(cs.convertId(id));
  }
   
  /*
   * Sends |s| to the |output|.
   */
  private void write(String s) throws IOException {
    if (output != null) {
      output.write(s);
    }
  }
  
  private void err(String e) {
    Err.error(lexer.name() + lexer.loc() + ": " + e);
  }

  
  /** Tests. */
  public static void main(String[] args) throws Exception {
    System.out.println("UserDefine = " + 
      TemplateToken.Case.PASCAL_CASE.convertId("user_define"));
    System.out.println("Generic = " + 
      TemplateToken.Case.PASCAL_CASE.convertId("generic"));
  }
}
