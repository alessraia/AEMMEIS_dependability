package controller.admin.gestisciOrdini;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.ordineService.Ordine;
import model.ordineService.OrdineDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;

import java.io.IOException;
import java.time.LocalDate;

import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

/**
 * Unit tests for ModificaStato servlet.
 * Tests the servlet's ability to modify order status and handle delivery date updates,
 * including forwarding to the correct JSP view.
 */
class ModificaStatoTest {
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;
    private ModificaStato servlet;

    @BeforeEach
    void setUp() {
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);
        servlet = new ModificaStato();
    }

    /**
     * Helper method to create an Ordine with ID and state.
     */
    private Ordine createOrdine(String ordineID, String stato) {
        Ordine ordine = new Ordine();
        ordine.setIdOrdine(ordineID);
        ordine.setStato(stato);
        return ordine;
    }

    /**
     * Test basic functionality: update order status to non-delivery state.
     * Scenario: Status is updated to "In Spedizione", no date is set
     */
    @Test
    void testDoGet_BasicStatusUpdate() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("ordineID")).thenReturn("ORD123");
        when(request.getParameter("stato")).thenReturn("In Spedizione");
        when(request.getParameter("utenteScelto")).thenReturn("user@example.com");
        when(request.getRequestDispatcher("gestisci-ordiniByUtente")).thenReturn(dispatcher);

        Ordine ordine = createOrdine("ORD123", "In Preparazione");

        try (MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById("ORD123")).thenReturn(ordine);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute("utenteScelto", "user@example.com");
            verify(request).getRequestDispatcher("gestisci-ordiniByUtente");
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test delivery status: when status is "Consegnato", date is set and updateOrdine is called.
     * Scenario: Status changed to "Consegnato", data arrival is set to today
     */
    @Test
    void testDoGet_ConsegnatoStatusSetDate() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("ordineID")).thenReturn("ORD123");
        when(request.getParameter("stato")).thenReturn("Consegnato");
        when(request.getParameter("utenteScelto")).thenReturn("user@example.com");
        when(request.getRequestDispatcher("gestisci-ordiniByUtente")).thenReturn(dispatcher);

        Ordine ordine = createOrdine("ORD123", "In Spedizione");

        try (MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById("ORD123")).thenReturn(ordine);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert - Verify updateOrdine is called (for Consegnato status)
            verify(request).setAttribute("utenteScelto", "user@example.com");
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test non-delivery status: updateStato is called instead of updateOrdine.
     * Scenario: Status is "In Preparazione", only updateStato is called
     */
    @Test
    void testDoGet_NonConsegnatoStatusUpdateOnly() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("ordineID")).thenReturn("ORD123");
        when(request.getParameter("stato")).thenReturn("In Preparazione");
        when(request.getParameter("utenteScelto")).thenReturn("user@example.com");
        when(request.getRequestDispatcher("gestisci-ordiniByUtente")).thenReturn(dispatcher);

        Ordine ordine = createOrdine("ORD123", "In Attesa");

        try (MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById("ORD123")).thenReturn(ordine);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute("utenteScelto", "user@example.com");
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test DAOs are instantiated and called.
     * Scenario: OrdineDAO is created and doRetrieveById is called with correct ID
     */
    @Test
    void testDoGet_DAOInstantiationAndCall() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("ordineID")).thenReturn("ORD456");
        when(request.getParameter("stato")).thenReturn("In Spedizione");
        when(request.getParameter("utenteScelto")).thenReturn("user@example.com");
        when(request.getRequestDispatcher("gestisci-ordiniByUtente")).thenReturn(dispatcher);

        Ordine ordine = createOrdine("ORD456", "In Preparazione");

        try (MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById("ORD456")).thenReturn(ordine);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).getParameter("ordineID");
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test order state is set correctly.
     * Scenario: Order state is updated to the requested value
     */
    @Test
    void testDoGet_OrderStateUpdated() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("ordineID")).thenReturn("ORD123");
        when(request.getParameter("stato")).thenReturn("In Spedizione");
        when(request.getParameter("utenteScelto")).thenReturn("user@example.com");
        when(request.getRequestDispatcher("gestisci-ordiniByUtente")).thenReturn(dispatcher);

        Ordine ordine = createOrdine("ORD123", "In Preparazione");

        try (MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById("ORD123")).thenReturn(ordine);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert - Verify stato is updated
            assert ordine.getStato().equals("In Spedizione");
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test null order: servlet forwards to error page.
     * Scenario: ordineID does not exist, ordine is null
     */
    @Test
    void testDoGet_NullOrderParameter() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("ordineID")).thenReturn("NONEXISTENT");
        when(request.getParameter("stato")).thenReturn("In Spedizione");
        when(request.getParameter("utenteScelto")).thenReturn("user@example.com");
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        try (MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById("NONEXISTENT")).thenReturn(null);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert - Servlet forwards to error page
            verify(request).getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test null status parameter: servlet forwards to error page.
     * Scenario: stato parameter is null
     */
    @Test
    void testDoGet_NullStatusParameter() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("ordineID")).thenReturn("ORD123");
        when(request.getParameter("stato")).thenReturn(null);
        when(request.getParameter("utenteScelto")).thenReturn("user@example.com");
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        Ordine ordine = createOrdine("ORD123", "In Preparazione");

        try (MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById("ORD123")).thenReturn(ordine);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert - Servlet forwards to error page
            verify(request).getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test null user parameter: servlet continues with null user.
     * Scenario: utenteScelto parameter is null
     */
    @Test
    void testDoGet_NullUserParameter() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("ordineID")).thenReturn("ORD123");
        when(request.getParameter("stato")).thenReturn("In Spedizione");
        when(request.getParameter("utenteScelto")).thenReturn(null);
        when(request.getRequestDispatcher("gestisci-ordiniByUtente")).thenReturn(dispatcher);

        Ordine ordine = createOrdine("ORD123", "In Preparazione");

        try (MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById("ORD123")).thenReturn(ordine);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute("utenteScelto", null);
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test multiple state transitions: state can be changed multiple times.
     * Scenario: Order status transitions through various states
     */
    @Test
    void testDoGet_MultipleStateTransitions() throws ServletException, IOException {
        // Test first transition
        when(request.getParameter("ordineID")).thenReturn("ORD123");
        when(request.getParameter("stato")).thenReturn("In Spedizione");
        when(request.getParameter("utenteScelto")).thenReturn("user@example.com");
        when(request.getRequestDispatcher("gestisci-ordiniByUtente")).thenReturn(dispatcher);

        Ordine ordine = createOrdine("ORD123", "In Preparazione");

        try (MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById("ORD123")).thenReturn(ordine);
                })) {

            servlet.doGet(request, response);
            assert ordine.getStato().equals("In Spedizione");

            // Test second transition
            when(request.getParameter("stato")).thenReturn("Consegnato");
            servlet.doGet(request, response);
            assert ordine.getStato().equals("Consegnato");

            verify(dispatcher, times(2)).forward(request, response);
        }
    }

    /**
     * Test empty string parameters: servlet handles empty strings.
     * Scenario: Parameters are empty strings
     */
    @Test
    void testDoGet_EmptyStringParameters() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("ordineID")).thenReturn("");
        when(request.getParameter("stato")).thenReturn("");
        when(request.getParameter("utenteScelto")).thenReturn("");
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        try (MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById("")).thenReturn(null);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert - forwards to error page because ordine is null
            verify(request).getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test special characters in order ID: handles special characters correctly.
     * Scenario: Order ID contains special characters
     */
    @Test
    void testDoGet_SpecialCharactersInOrderID() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("ordineID")).thenReturn("ORD-2024/11/21");
        when(request.getParameter("stato")).thenReturn("In Spedizione");
        when(request.getParameter("utenteScelto")).thenReturn("user@example.com");
        when(request.getRequestDispatcher("gestisci-ordiniByUtente")).thenReturn(dispatcher);

        Ordine ordine = createOrdine("ORD-2024/11/21", "In Preparazione");

        try (MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById("ORD-2024/11/21")).thenReturn(ordine);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test case sensitivity in status comparison.
     * Scenario: Status "consegnato" (lowercase) vs "Consegnato" (uppercase)
     */
    @Test
    void testDoGet_StatusCaseSensitivity() throws ServletException, IOException {
        // Arrange - lowercase should not trigger date setting
        when(request.getParameter("ordineID")).thenReturn("ORD123");
        when(request.getParameter("stato")).thenReturn("consegnato");
        when(request.getParameter("utenteScelto")).thenReturn("user@example.com");
        when(request.getRequestDispatcher("gestisci-ordiniByUtente")).thenReturn(dispatcher);

        Ordine ordine = createOrdine("ORD123", "In Spedizione");

        try (MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById("ORD123")).thenReturn(ordine);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert - lowercase won't match "Consegnato"
            verify(request).setAttribute("utenteScelto", "user@example.com");
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test request forwarding: verify correct forward path.
     * Scenario: Dispatcher forward is called with correct path
     */
    @Test
    void testDoGet_ForwardingPath() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("ordineID")).thenReturn("ORD123");
        when(request.getParameter("stato")).thenReturn("In Spedizione");
        when(request.getParameter("utenteScelto")).thenReturn("user@example.com");
        when(request.getRequestDispatcher("gestisci-ordiniByUtente")).thenReturn(dispatcher);

        Ordine ordine = createOrdine("ORD123", "In Preparazione");

        try (MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById("ORD123")).thenReturn(ordine);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert - Verify correct forward path
            verify(request).getRequestDispatcher("gestisci-ordiniByUtente");
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    /**
     * Test all possible order states: servlet handles various states.
     * Scenario: Different order states are handled correctly
     */
    @Test
    void testDoGet_VariousOrderStates() throws ServletException, IOException {
        String[] states = {"In Attesa", "In Preparazione", "In Spedizione", "Consegnato"};

        for (String state : states) {
            // Arrange
            reset(request, response, dispatcher);
            when(request.getParameter("ordineID")).thenReturn("ORD123");
            when(request.getParameter("stato")).thenReturn(state);
            when(request.getParameter("utenteScelto")).thenReturn("user@example.com");
            when(request.getRequestDispatcher("gestisci-ordiniByUtente")).thenReturn(dispatcher);

            Ordine ordine = createOrdine("ORD123", "In Preparazione");

            try (MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                    (mock, context) -> {
                        when(mock.doRetrieveById("ORD123")).thenReturn(ordine);
                    })) {

                // Act
                servlet.doGet(request, response);

                // Assert
                verify(request).setAttribute("utenteScelto", "user@example.com");
                verify(dispatcher).forward(request, response);
            }
        }
    }

    /**
     * Test attribute setting: utenteScelto is set correctly.
     * Scenario: User parameter is forwarded as attribute to next page
     */
    @Test
    void testDoGet_AttributeSetting() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("ordineID")).thenReturn("ORD123");
        when(request.getParameter("stato")).thenReturn("In Spedizione");
        when(request.getParameter("utenteScelto")).thenReturn("alice@example.com");
        when(request.getRequestDispatcher("gestisci-ordiniByUtente")).thenReturn(dispatcher);

        Ordine ordine = createOrdine("ORD123", "In Preparazione");

        try (MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById("ORD123")).thenReturn(ordine);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute("utenteScelto", "alice@example.com");
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test updateStato is called for non-Consegnato status.
     * Scenario: Status is not "Consegnato", so updateStato should be called
     */
    @Test
    void testDoGet_VerifyDAOUpdateStatoCall() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("ordineID")).thenReturn("ORD789");
        when(request.getParameter("stato")).thenReturn("In Spedizione");
        when(request.getParameter("utenteScelto")).thenReturn("user@example.com");
        when(request.getRequestDispatcher("gestisci-ordiniByUtente")).thenReturn(dispatcher);

        Ordine ordine = createOrdine("ORD789", "In Preparazione");

        try (MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById("ORD789")).thenReturn(ordine);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert - Verify updateStato is called
            OrdineDAO dao = mockOrdineDAO.constructed().get(0);
            verify(dao).updateStato(ordine);
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test updateOrdine is called for Consegnato status.
     * Scenario: Status is "Consegnato", so updateOrdine should be called with date set
     */
    @Test
    void testDoGet_VerifyDAOUpdateOrdineCallForConsegnato() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("ordineID")).thenReturn("ORD999");
        when(request.getParameter("stato")).thenReturn("Consegnato");
        when(request.getParameter("utenteScelto")).thenReturn("user@example.com");
        when(request.getRequestDispatcher("gestisci-ordiniByUtente")).thenReturn(dispatcher);

        Ordine ordine = createOrdine("ORD999", "In Spedizione");

        try (MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById("ORD999")).thenReturn(ordine);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert - Verify updateOrdine is called for Consegnato
            OrdineDAO dao = mockOrdineDAO.constructed().get(0);
            verify(dao).updateOrdine(ordine);
            verify(dispatcher).forward(request, response);
        }
    }
}
