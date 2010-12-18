vim:filetype=java:

\def{mtn}{\MemberType \memberName}

\file{Generated.java}
\classes{
class \ClassName {
  \members{private \mtn;}
  public \ClassName make(\members[,]{\mtn}) { 
    \members{this.\memberName = \memberName;} 
  }
  \members{
    public with\MemberName(\mtn) {
      return make(\members[,]{\memberName});
    }
  }
}
}
