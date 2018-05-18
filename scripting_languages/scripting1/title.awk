BEGIN {                     # λέξεις "θόρυβος"
    nw["a"] = 1;    nw["an"] = 1;   nw["and"] = 1;  nw["but"] = 1
    nw["by"] = 1;   nw["for"] = 1;  nw["from"] = 1; nw["in"] = 1
    nw["into"] = 1; nw["nor"] = 1;  nw["of"] = 1;   nw["on"] = 1
    nw["or"] = 1;   nw["over"] = 1; nw["the"] = 1;  nw["to"] = 1
    nw["via"] = 1;  nw["with"] = 1
}
{
  for (i=1; i <= NF; i++) {
    if ((!nw[$i] || i == 0 || $(i-1) ~ /[:-]$/) && ($i !~ /.+[A-Z]/)) {
      # μετατροπή σε κεφαλαίο
      $i = toupper(substr($i, 1, 1)) substr($i, 2)
   }
   printf $i " ";      # μην προσθέσεις αλλαγή γραμμής
  }
  printf "\n";
}
