vim:ft=java:

This template generates code for AST classes.

\def{smt}{\if_primitive{\Membertype}{\MemberType}}
\def{mt}{\if_tagged{list}{ImmutableList<}{}\smt\if_tagged{list}{>}{}}
\def{mtn}{\mt \memberName}
\def{mtn_list}{\members[,]{\mtn}}

\classes{\file{\ClassName.java}
/** Do NOT edit. See classes.tpl instead. */
package freeboogie.ast;

import com.google.common.base.Supplier;
import com.google.common.collect.ImmutableList;
import genericutils.Logger;

import static freeboogie.cli.FbCliOptionsInterface.*;

/** @author rgrig */
public \if_terminal{final}{abstract} class \ClassName extends \BaseName {
  \enums{public static enum \EnumName {\values[,]{\VALUE_NAME}}}
\if_terminal{
  \members{private final \mtn;}

  // === construction ===
  private \ClassName(\mtn_list) {
    this(\members[,]{\memberName}, FileLocation.unknown());
    log.say(LogCategories.AST, LogLevel.WARNING, new Supplier<String>() {
      @Override public String get() {
        StackTraceElement[] stack = new Exception().getStackTrace();
        for (int i = 1; i < stack.length; ++i) {
          if (stack[i-1].getMethodName().equals("mk"))
            return stack[i].toString();
        }
        return "unknown invocation of mk() without location";
      }
    });
  }

  private \ClassName(\mtn_list, FileLocation location) {
    this.location = location;
    \members{
      \if_tagged{list}{
        this.\memberName = \memberName == null? 
            ImmutableList.<\smt>of() : 
            \memberName;
      }{
        this.\memberName = \memberName;
      }
    }
    checkInvariant();
  }
  
  // TODO(radugrigore): perhaps drop this method so that file
  // location always has to be provided explicitely (even if it
  // is FileLocation.unknown()).
  public static \ClassName mk(\mtn_list) {
    return new \ClassName(\members[,]{\memberName});
  }

  public static \ClassName mk(\mtn_list, FileLocation location) {
    return new \ClassName(\members[,]{\memberName}, location);
  }

  \members{
    public \ClassName with\MemberName(\mtn) {
      return \memberName == this.\memberName? this : mk(\members[,]{\memberName}, location);
    }
  }

  public void checkInvariant() {
    assert location != null;
    \members{
      \if_tagged{nonnull|list}{assert \memberName != null;}{}
    }
    \invariants{assert \inv;}
  }
}{}

  // === accessors ===
  \if_terminal{
    \members{public \mtn() { return \memberName; }}
  }{
    \selfmembers{public abstract \mtn();}
  }

\if_terminal{
  @Override public ImmutableList<Ast> children() {
    if (children != null) return children;
    ImmutableList.Builder<Ast> builder_ = ImmutableList.builder();
    \children{
      \if_tagged{list}{
        builder_.addAll(\memberName);
      }{
        if (\memberName != null) builder_.add(\memberName);
      }
    }
    children = builder_.build();
    return children;
  }
}{}

\if_terminal{
  // === the Visitor pattern ===
  @Override
  public <R> R eval(Evaluator<R> evaluator) { 
    return evaluator.eval(this); 
  }
}{}

\if_terminal{
  // === others ===
  @Override public \ClassName clone() {
    \members{
      \if_primitive{
        \mt new\MemberName = this.\memberName;
      }{
        \if_tagged{list}{
          \mt new\MemberName = AstUtils.cloneListOf\MemberType(\memberName);
        }{
          \mt new\MemberName = this.\memberName == null? 
              null : this.\memberName.clone();
        }
      }
    }
    return \ClassName.mk(\members[, ]{new\MemberName}, location);
  }
}{
  @Override public abstract \ClassName clone();
}

\if_terminal{
  public String toString() {
    return "[\ClassName<" + hash() + 
        "> "+ \members[ + " " + ]{\memberName} + "]";
  }
}{}}
