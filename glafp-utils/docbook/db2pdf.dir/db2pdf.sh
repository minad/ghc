if [ ! -f "$DOCBOOK_CATALOG" ] ; then
  echo "CATALOG file not set up; see installation guide for details."
  exit 1
fi

# Dave Mason's option to specify a different stylesheet
case $1 in
    -d) DB_STYLESHEET=$2
        shift 2
	;;
esac

echo "Using stylesheet: \"${DB_STYLESHEET}\""

if [ $# -gt 2 ]
then
  echo "Usage: `basename $0` [filename.sgml]" >&2
  exit 1
fi

if [ $# -eq 1 ]
then
  if [ ! -r $1 ]
  then
    echo Cannot read \"$1\".  Exiting. >&2
    exit 1
  fi
  if echo $1 | egrep -i '\.sgml$|\.sgm$' >/dev/null 2>&1
  then
    output="`echo $1 | sed 's,\.sgml$,,;s,\.sgm$,,'`"
  fi
fi

# assumption: openjade and pdfjadetex is installed in the same dir.
PDFJADETEX=`dirname $JADE`/pdfjadetex

$JADE -t tex -d ${DB_STYLESHEET}\#print -o ${output}.tex -c $DOCBOOK_CATALOG $1

${PDFJADETEX} ${output}

# See if running pdfjadetex twice cures the problem.
if egrep '^LaTeX Warning: There were undefined references.$' ${TMPFN}.log >/dev/null 2>&1
then
  ${PDFJADETEX} ${output}
  ${PDFJADETEX} ${output}
fi

# clean out 
rm -f ${output}.log
rm -f ${output}.aux
rm -f ${output}.tex

exit 0
