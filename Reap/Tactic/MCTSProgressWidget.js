import * as React from 'react';
import { EditorContext, useRpcSession, mapRpcError } from '@leanprover/infoview';
const e = React.createElement;

function displayProgress(progress) {
  return '[' + (progress.step || 0) + '/' + (progress.maxSteps || 0) + ']';
}

function shouldPoll(progress) {
  return !progress.done || (progress.solved && !progress.script);
}

export default function(props) {
  const rs = useRpcSession();
  const editorConnection = React.useContext(EditorContext);
  const [progress, setProgress] = React.useState(props.initial);
  const [error, setError] = React.useState(null);

  React.useEffect(() => {
    let cancelled = false;
    let timer = null;

    async function poll() {
      try {
        const next = await rs.call('getReapMCTSProgress', { id: props.id });
        if (cancelled) return;
        setProgress(next);
        setError(null);
        if (shouldPoll(next)) {
          timer = window.setTimeout(poll, 300);
        }
      } catch (err) {
        if (cancelled) return;
        setError(mapRpcError(err).message);
        timer = window.setTimeout(poll, 1000);
      }
    }

    poll();
    return () => {
      cancelled = true;
      if (timer !== null) window.clearTimeout(timer);
    };
  }, [rs, props.id]);

  const statusColor = progress.solved
    ? 'var(--vscode-testing-iconPassed)'
    : progress.done
      ? 'var(--vscode-descriptionForeground)'
      : 'var(--vscode-progressBar-background)';
  const goal = progress.goalType || 'starting';
  function onClick() {
    if (!progress.script) return;
    editorConnection.api.applyEdit({
      changes: { [props.pos.uri]: [{ range: props.range, newText: progress.script }] }
    });
  }
  function tryThis() {
    if (!progress.script) return null;
    return e('div',
      {
        className: 'font-code pre-wrap',
        style: {
          marginTop: '0.5em',
          whiteSpace: 'pre-wrap',
          overflowWrap: 'anywhere'
        }
      },
      e('div', null, 'Try this:'),
      e('div', null,
        e('span',
          {
            onClick,
            title: 'Apply suggestion',
            className: 'link pointer dim font-code',
            style: { color: 'var(--vscode-textLink-foreground)' }
          },
          '[apply]'),
        ' ',
        e('span', null, progress.script)))
  }

  return e('div',
    {
      className: 'ml1 font-code pre-wrap',
      style: { overflowWrap: 'anywhere' }
    },
    e('div',
      {
        style: {
          display: 'flex',
          gap: '0.5em',
          alignItems: 'baseline',
          overflowWrap: 'anywhere'
        }
      },
      e('span', { style: { color: statusColor, fontWeight: 600 } }, progress.status || 'running'),
      e('span', { style: { color: statusColor, fontWeight: 600 } }, displayProgress(progress)),
      e('span', null, goal),
      error ? e('span', { style: { color: 'var(--vscode-errorForeground)' } }, error) : null
    ),
    tryThis()
  );
}
