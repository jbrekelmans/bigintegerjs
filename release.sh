#!/bin/bash -e
# Requires https://stedolan.github.io/jq/

#Helper functions
function strjoin { local IFS="$1"; shift; echo "$*"; }
function strstartswith {
  local b_len="${#2}"
  if [ "${#1}" -lt "$b_len" ] || [ "${1:0:$b_len}" != "$2" ]; then
    echo "0"
  else
    echo "1"
  fi
}
function str_fromJsonStringLiteral {
  local x="$1"
  x="$(sed 's/^"\(.*\)"$/\1/' <<< "$x")"
  echo "$x"
}

# Parse arguments
allReleaseTypes=(major minor patch)
indexOfReleaseType=2
while [[ $# -gt 0 ]]
do
    if [[ $# -gt 1 ]]; then
        key="$1"
        case $key in
            -rt|--release_type)
            releaseType="$(tr '[A-Z]' '[a-z]' <<< "$2")"
            indexOfReleaseType=-1
            for i in "${!allReleaseTypes[@]}"; do
                if [[ "${allReleaseTypes[$i]}" = "$releaseType" ]]; then
                    indexOfReleaseType=$i
                    break
                fi
            done
            if [[ "$indexOfReleaseType" -lt 0 ]]; then
                echo "Release type must be one of (ignoring case) 'major', 'minor' and 'patch'"
            fi
            shift
            shift
            continue
            ;;
            *)
            # Unknown option
            echo "Got potential key-value pair argument but could not recognize key: $key $2"
            ;;
        esac
    fi
    if [[ $# -gt 0 ]]; then
        case $key in
            *)
            # Unknown option
            echo "Got single argument, but could not recognize it: $1"
            shift
            ;;
        esac
    fi
done

if [[ "$indexOfReleaseType" -lt 0 ]]; then
    exit 1
fi
packageJsonFileName="./package.json"

# Get version
verstr="$(jq '.version' < "$packageJsonFileName")"
verstr="$(str_fromJsonStringLiteral "$verstr")"
if [[ ! "$verstr" =~ ^[0-9]+(\.[0-9]+){2}$ ]]; then
    echo "Version string in $packageJsonFileName did not match ^[0-9]+(\.[0-9]+){2}$"
    exit 1
fi
IFS='.' read -r -a ver <<< "$verstr"

# Increment version
verx="${ver[$indexOfReleaseType]}"
((verx+=1))
ver[$indexOfReleaseType]="$verx"
for ((i=$indexOfReleaseType+1;i<=2;i++)); do
    ver[$i]="0"
done
verstr="$(strjoin '.' ${ver[@]})"

jqexpr=".version=\"$verstr\""
cp "$packageJsonFileName" "$packageJsonFileName.bak"


jq "$jqexpr" < "$packageJsonFileName.bak" > "$packageJsonFileName"

git push
git tag "$verstr"
git push --tags

npm publish

rm "$packageJsonFileName.bak"
