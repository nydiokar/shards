-module(shard_telecom_app).
-behaviour(application).

-export([start/2, stop/1]).

start(_Type, _Args) ->
    shard_telecom_sup:start_link().

stop(_State) ->
    ok.


-module(shard_fax).
-behaviour(gen_server).
-export([start_link/1, send_fax/3]).
-export([init/1, handle_call/3]).

start_link(Shard) ->
    gen_server:start_link({local, ?MODULE}, ?MODULE, [Shard], []).

send_fax(RemoteShard, ImagePath, Resolution) ->
    gen_server:call(?MODULE, {send_fax, RemoteShard, ImagePath, Resolution}).

init([Shard]) ->
    {ok, #{shard => Shard, resolution => standard, encoding => mh}}.

handle_call({send_fax, Remote, ImagePath, Resolution}, _From, State) ->
    %% Simplified fax transmission
    io:format("Sending fax from shard ~p to ~p: ~s~n", 
              [maps:get(shard, State), Remote, ImagePath]),
    {reply, {ok, 1}, State}.
