# Generation of UPPAAL Timed Automata Models from RIAPS Coponent Code

## Overview
The RIAPS2UPPAAL framework is designed to convert distributed application models defined in the RIAPS framework into a network of timed automata that can be analyzed using UPPAAL. The conversion process involves parsing, model generation, and model merging stages. This framework abstracts away low-level details and focuses on the application-level logical architecture, component interactions, and timing properties.

## Model Generation Process
1. **Parsing Stage** 
- *Input*: RIAPS application model (app.riaps) and deployment configuration (app.depl).
- *Process*: The parser extracts information about distributed components, their ports, message types, and deployment to remote platforms. This information is used to determine global variables, template definitions, and their associated parameters.
3. **Model Generation Stage** 
- *Input*: Parsed data from the RIAPS model.
- *Process*: Timed automata (TA) definitions are generated based on component instances, port types, and component implementation code in Python. The framework handles various communication patterns like synchronous request-response, asynchronous query-answer, and publish-subscribe, with specific TA templates for each.
4. **Model Merging Stage**
*Input*: Generated TA templates and process definitions.
*Process*: The generated templates and process definitions are merged into a single .xta file. This file is structured for compatibility with UPPAAL and captures the logical architecture and timing behavior of the application.

## Interaction Patterns and Component Models
- *Urgent Transitions*: Implemented using additional automata with synchronization labels to force immediate transitions, mimicking software instruction behavior.
- *Port Queues and Timers*: Modeled using custom data structures and synchronization patterns to handle message passing and timing events.
- *Component Automata*: Generated dynamically based on parsed models and source code, incorporating timing information from user annotations.

## Scheduler Models
- *Component Schedule*r: Regulates the processing of incoming messages in the distributed system. The scheduler automaton, dynamically generated, manages the invocation of port handler methods based on different scheduling policies like batch, round-robin, and priority scheduling.

## Example: RelayManager
### Description
Consider the RelayManager component, which is part of a RIAPS application model named RelayMonitor. The component has two ports: a subscribe port RecvRelayStatus and a sporadic timer countdown. The application model also defines an actor RelayManager and its deployment configuration, which maps an instance of the RelayManager actor to a host (h1).

The RelayManager component receives messages indicating the status of a relay device, commonly used in electrical distribution networks. When a status message is received, the component starts the countdown timer. If another message is received before the timer expires, the timer is reset; otherwise, the timer handler is invoked, indicating a timeout.

### Generated TA Model
The RIAPS2UPPAAL framework generates a TA model for the RelayManager component:

- Initial Location: ready
- Port Handlers: Two outgoing edges lead to on_countdown_45 and on_RecvRelayStatus_22, representing the two port handlers, respectively.
- Model Patterns: The model includes operations for sending and receiving messages, launching and canceling timers, and setting delays on the timer countdown.
### Usage
To use the RIAPS2UPPAAL framework:

- Prepare RIAPS Model: Ensure that the application model (app.riaps) and deployment configuration (app.depl) are correctly defined.
- Run the Framework: Execute the provided scripts to generate the UPPAAL-compatible TA model.
- Verify with UPPAAL: Import the generated app.xta file into UPPAAL for simulation and verification.
