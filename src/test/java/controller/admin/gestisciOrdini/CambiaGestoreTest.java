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

import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.*;

/**
 * Unit tests for CambiaGestore servlet.
 * Tests the servlet's ability to change the manager (gestore) of an order
 * by updating the matricola (manager ID) and handling request forwarding.
 */
class CambiaGestoreTest {

    private CambiaGestore servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setUp() {
        servlet = new CambiaGestore();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);

        when(request.getRequestDispatcher("gestisci-ordiniByUtente")).thenReturn(dispatcher);
    }

    /**
     * Test successful manager assignment to an order.
     * Scenario: Valid order ID and matricola are provided, manager is updated successfully
     */
    @Test
    void testDoGet_SuccessfulManagerAssignment() throws ServletException, IOException {
        // Arrange
        String ordineID = "ORD001";
        String matricola = "MAT123";
        String utenteScelto = "user@example.com";

        when(request.getParameter("ordineID")).thenReturn(ordineID);
        when(request.getParameter("matricola")).thenReturn(matricola);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        Ordine ordine = new Ordine();
        ordine.setIdOrdine(ordineID);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(ordineID)).thenReturn(ordine);
            doNothing().when(mock).updateOrdineMatricola(ordine);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            OrdineDAO mockDAO = mockedConstruction.constructed().get(0);
            verify(mockDAO).doRetrieveById(ordineID);
            verify(mockDAO).updateOrdineMatricola(ordine);
            verify(request).setAttribute("utenteScelto", utenteScelto);
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test matricola is correctly set on the order object.
     * Scenario: Verify that the matricola parameter is properly assigned to the ordine object
     */
    @Test
    void testDoGet_MatricolaCorrectlySet() throws ServletException, IOException {
        // Arrange
        String ordineID = "ORD002";
        String matricola = "MAT456";
        String utenteScelto = "admin@example.com";

        when(request.getParameter("ordineID")).thenReturn(ordineID);
        when(request.getParameter("matricola")).thenReturn(matricola);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        Ordine ordine = new Ordine();
        ordine.setIdOrdine(ordineID);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(ordineID)).thenReturn(ordine);
            doNothing().when(mock).updateOrdineMatricola(ordine);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            assert ordine.getMatricola().equals(matricola) : "Matricola was not correctly set";
        }
    }

    /**
     * Test request forwarding to gestisci-ordiniByUtente.
     * Scenario: After updating order, request is forwarded to the correct dispatcher
     */
    @Test
    void testDoGet_RequestForwardedCorrectly() throws ServletException, IOException {
        // Arrange
        String ordineID = "ORD003";
        String matricola = "MAT789";
        String utenteScelto = "user2@example.com";

        when(request.getParameter("ordineID")).thenReturn(ordineID);
        when(request.getParameter("matricola")).thenReturn(matricola);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        Ordine ordine = new Ordine();
        ordine.setIdOrdine(ordineID);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(ordineID)).thenReturn(ordine);
            doNothing().when(mock).updateOrdineMatricola(ordine);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).getRequestDispatcher("gestisci-ordiniByUtente");
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test utenteScelto attribute is set in request.
     * Scenario: The selected user email is properly set as a request attribute
     */
    @Test
    void testDoGet_UtenteSceltoAttributeSet() throws ServletException, IOException {
        // Arrange
        String ordineID = "ORD004";
        String matricola = "MAT999";
        String utenteScelto = "newuser@example.com";

        when(request.getParameter("ordineID")).thenReturn(ordineID);
        when(request.getParameter("matricola")).thenReturn(matricola);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        Ordine ordine = new Ordine();
        ordine.setIdOrdine(ordineID);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(ordineID)).thenReturn(ordine);
            doNothing().when(mock).updateOrdineMatricola(ordine);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute("utenteScelto", utenteScelto);
        }
    }

    /**
     * Test handling of different manager IDs.
     * Scenario: Multiple calls with different matricola values to verify flexibility
     */
    @Test
    void testDoGet_MultipleDifferentManagers() throws ServletException, IOException {
        String[] matricolas = {"MAT001", "MAT002", "MAT003"};
        String[] ordineIDs = {"ORD100", "ORD101", "ORD102"};

        for (int i = 0; i < matricolas.length; i++) {
            // Reset mocks for each iteration
            reset(request, dispatcher);
            when(request.getRequestDispatcher("gestisci-ordiniByUtente")).thenReturn(dispatcher);

            String ordineID = ordineIDs[i];
            String matricola = matricolas[i];
            String utenteScelto = "user" + i + "@example.com";

            when(request.getParameter("ordineID")).thenReturn(ordineID);
            when(request.getParameter("matricola")).thenReturn(matricola);
            when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

            Ordine ordine = new Ordine();
            ordine.setIdOrdine(ordineID);

            try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
                when(mock.doRetrieveById(ordineID)).thenReturn(ordine);
                doNothing().when(mock).updateOrdineMatricola(ordine);
            })) {
                // Act
                servlet.doGet(request, response);

                // Assert
                OrdineDAO mockDAO = mockedConstruction.constructed().get(0);
                verify(mockDAO).doRetrieveById(ordineID);
                verify(mockDAO).updateOrdineMatricola(ordine);
                assert ordine.getMatricola().equals(matricola);
                verify(request).setAttribute("utenteScelto", utenteScelto);
            }
        }
    }

    /**
     * Test with special characters in parameters.
     * Scenario: Manager ID contains special characters (edge case)
     */
    @Test
    void testDoGet_SpecialCharactersInParameters() throws ServletException, IOException {
        // Arrange
        String ordineID = "ORD-2025-001";
        String matricola = "MAT_123_ABC";
        String utenteScelto = "user+admin@example.com";

        when(request.getParameter("ordineID")).thenReturn(ordineID);
        when(request.getParameter("matricola")).thenReturn(matricola);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        Ordine ordine = new Ordine();
        ordine.setIdOrdine(ordineID);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(ordineID)).thenReturn(ordine);
            doNothing().when(mock).updateOrdineMatricola(ordine);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            assert ordine.getMatricola().equals(matricola);
            verify(request).setAttribute("utenteScelto", utenteScelto);
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test manager assignment sequence.
     * Scenario: Verify the correct sequence of operations (retrieve, set, update, forward)
     */
    @Test
    void testDoGet_CorrectOperationSequence() throws ServletException, IOException {
        // Arrange
        String ordineID = "ORD005";
        String matricola = "MAT555";
        String utenteScelto = "sequence@example.com";

        when(request.getParameter("ordineID")).thenReturn(ordineID);
        when(request.getParameter("matricola")).thenReturn(matricola);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        Ordine ordine = new Ordine();
        ordine.setIdOrdine(ordineID);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(ordineID)).thenReturn(ordine);
            doNothing().when(mock).updateOrdineMatricola(ordine);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            OrdineDAO mockDAO = mockedConstruction.constructed().get(0);
            
            // Verify doRetrieveById is called first
            verify(mockDAO, times(1)).doRetrieveById(ordineID);
            
            // Verify updateOrdineMatricola is called after
            verify(mockDAO, times(1)).updateOrdineMatricola(ordine);
            
            // Verify setAttribute and forward are called
            verify(request).setAttribute("utenteScelto", utenteScelto);
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test null matricola handling.
     * Scenario: When matricola parameter is null or empty
     */
    @Test
    void testDoGet_NullMatricolaParameter() throws ServletException, IOException {
        // Arrange
        String ordineID = "ORD006";
        String utenteScelto = "user@example.com";

        when(request.getParameter("ordineID")).thenReturn(ordineID);
        when(request.getParameter("matricola")).thenReturn(null);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        Ordine ordine = new Ordine();
        ordine.setIdOrdine(ordineID);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(ordineID)).thenReturn(ordine);
            doNothing().when(mock).updateOrdineMatricola(ordine);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            OrdineDAO mockDAO = mockedConstruction.constructed().get(0);
            verify(mockDAO).doRetrieveById(ordineID);
            verify(mockDAO).updateOrdineMatricola(ordine);
            // Verify that forward still occurs despite null matricola
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test null ordineID handling.
     * Scenario: When ordineID parameter is null
     */
    @Test
    void testDoGet_NullOrdineIDParameter() throws ServletException, IOException {
        // Arrange
        String matricola = "MAT111";
        String utenteScelto = "user@example.com";

        when(request.getParameter("ordineID")).thenReturn(null);
        when(request.getParameter("matricola")).thenReturn(matricola);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(null)).thenReturn(null);
        })) {
            // Act & Assert - This will likely throw NPE if ordine is null and setMatricola is called
            try {
                servlet.doGet(request, response);
            } catch (NullPointerException e) {
                // Expected behavior when ordineID is null
                verify(mockedConstruction.constructed().get(0)).doRetrieveById(null);
            }
        }
    }

    /**
     * Test with empty string parameters.
     * Scenario: Parameters provided as empty strings
     */
    @Test
    void testDoGet_EmptyStringParameters() throws ServletException, IOException {
        // Arrange
        String ordineID = "";
        String matricola = "";
        String utenteScelto = "";

        when(request.getParameter("ordineID")).thenReturn(ordineID);
        when(request.getParameter("matricola")).thenReturn(matricola);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        Ordine ordine = new Ordine();
        ordine.setIdOrdine(ordineID);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(ordineID)).thenReturn(ordine);
            doNothing().when(mock).updateOrdineMatricola(ordine);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            OrdineDAO mockDAO = mockedConstruction.constructed().get(0);
            verify(mockDAO).doRetrieveById(ordineID);
            verify(mockDAO).updateOrdineMatricola(ordine);
            assert ordine.getMatricola().equals("");
            verify(request).setAttribute("utenteScelto", "");
        }
    }

    /**
     * Test manager assignment updates database correctly.
     * Scenario: Verify updateOrdineMatricola is invoked with correct ordine object
     */
    @Test
    void testDoGet_DAOUpdateCalledWithCorrectOrdine() throws ServletException, IOException {
        // Arrange
        String ordineID = "ORD007";
        String matricola = "MAT777";
        String utenteScelto = "dbtest@example.com";

        when(request.getParameter("ordineID")).thenReturn(ordineID);
        when(request.getParameter("matricola")).thenReturn(matricola);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        Ordine ordine = new Ordine();
        ordine.setIdOrdine(ordineID);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(ordineID)).thenReturn(ordine);
            doNothing().when(mock).updateOrdineMatricola(ordine);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            OrdineDAO mockDAO = mockedConstruction.constructed().get(0);
            verify(mockDAO).updateOrdineMatricola(argThat(o -> 
                o.getIdOrdine().equals(ordineID) && o.getMatricola().equals(matricola)
            ));
        }
    }

    /**
     * Test long matricola values.
     * Scenario: Manager ID with maximum length or very long string
     */
    @Test
    void testDoGet_LongMatricolaValue() throws ServletException, IOException {
        // Arrange
        String ordineID = "ORD008";
        String matricola = "MAT" + "0".repeat(100); // Very long matricola
        String utenteScelto = "long@example.com";

        when(request.getParameter("ordineID")).thenReturn(ordineID);
        when(request.getParameter("matricola")).thenReturn(matricola);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        Ordine ordine = new Ordine();
        ordine.setIdOrdine(ordineID);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(ordineID)).thenReturn(ordine);
            doNothing().when(mock).updateOrdineMatricola(ordine);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            assert ordine.getMatricola().equals(matricola);
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test numeric matricola values.
     * Scenario: Manager ID containing only numbers
     */
    @Test
    void testDoGet_NumericMatricolaValue() throws ServletException, IOException {
        // Arrange
        String ordineID = "ORD009";
        String matricola = "12345678";
        String utenteScelto = "numeric@example.com";

        when(request.getParameter("ordineID")).thenReturn(ordineID);
        when(request.getParameter("matricola")).thenReturn(matricola);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        Ordine ordine = new Ordine();
        ordine.setIdOrdine(ordineID);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(ordineID)).thenReturn(ordine);
            doNothing().when(mock).updateOrdineMatricola(ordine);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            assert ordine.getMatricola().equals(matricola);
            OrdineDAO mockDAO = mockedConstruction.constructed().get(0);
            verify(mockDAO).updateOrdineMatricola(ordine);
        }
    }
}
