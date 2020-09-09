#!/bin/bash

# basic settings
model=$3
cmax=$4
primary_method=$1
secondary_method="lift"

regime=$2

# hybrid method parameters
threshold=$5
cegar_iters_limit=$6
cegis_expanded_per_iter=$7

# explore parameters
t_min=0.00
t_max=$8
t_step=$9

l_min=1
l_max=50
l_step=2

e_min=1
e_max=500
e_step=10

# do not change the following
workspace="workspace"
examples_dir="${workspace}/examples"
experiments_dir="${workspace}/experiments"
parameters_file="${experiments_dir}/parameters.txt"
log_file="${experiments_dir}/log.txt"
log_grep_file="${experiments_dir}/log_grep.txt"

function write_params {
    echo "$regime" > $parameters_file
    echo "$cegar_iters_limit" >> $parameters_file
    echo "$cegis_expanded_per_iter" >> $parameters_file
}

function dynasty {
    write_params
    dynasty_opts="--project ${examples_dir}/${model}/ --sketch sketch.templ --allowed sketch.allowed --properties sketch.properties"
    dynasty="python dynasty.py ${dynasty_opts} ${primary_method}"
    timeout 600s ${dynasty} --constants "CMAX=${cmax},THRESHOLD=${threshold}"
    if [ $? -eq  124 ]
    then
      dynasty="python dynasty.py ${dynasty_opts} ${secondary_method}"
      timeout 600s ${dynasty} --constants "CMAX=${cmax},THRESHOLD=${threshold}"
    fi
}

# reset files
echo "" > ${log_file}
echo "" > ${log_grep_file}
write_params

# experiments section
if [ "$regime" -eq 0 ] # simple execution
then
    dynasty
    exit
elif [ "$regime" -eq 1 ] # explore threshold
then
    for threshold in `seq ${t_min} ${t_step} ${t_max}`; do
        echo -n "${threshold}, " | tee --append ${log_file} | tail -1 | tee --append ${log_grep_file}
        dynasty | tee --append ${log_file} | tail -1 | tee --append ${log_grep_file}
    done
elif [ "$regime" -eq 2 ] # explore cegar iterations limit
then
    # shellcheck disable=SC2006
    for cegar_iters_limit in `seq ${l_min} ${l_step} ${l_max}`; do
        echo -n "${cegar_iters_limit}, "  | tee --append ${log_file} | tail -1 | tee --append ${log_grep_file}
        write_params
        dynasty | tee --append ${log_file} | tail -1 | tee --append ${log_grep_file}
    done
elif [ "$regime" -eq 3 ] # explore expanded per iter
then
    # shellcheck disable=SC2006
    for cegis_expanded_per_iter in `seq ${e_min} ${e_step} ${e_max}`; do
        echo -n "${cegis_expanded_per_iter}, "  | tee --append ${log_file} | tail -1 | tee --append ${log_grep_file}
        write_params
        dynasty | tee --append ${log_file} | tail -1 | tee --append ${log_grep_file}
    done
else
    echo "what"
fi

paplay /usr/share/sounds/freedesktop/stereo/complete.oga

# subl ${log_file}
# subl ${log_grep_file}