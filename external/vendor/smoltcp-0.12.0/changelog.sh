for pr in $(git log v0.11.0..main --grep 'Merge' | grep -oP '#[0-9]+' | sort -u); do 
    echo $(gh pr view $pr --json title -q .title) "([$pr](https://github.com/smoltcp-rs/smoltcp/pull/$pr))"
done
