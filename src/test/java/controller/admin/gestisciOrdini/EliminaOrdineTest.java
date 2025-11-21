package controller.admin.gestisciOrdini;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.ordineService.OrdineDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;

import java.io.IOException;

import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.*;

/**
 * Unit tests for EliminaOrdine servlet.
 * Tests the servlet's ability to delete orders (ordini) from the system
 * and handle request forwarding after deletion.
 */
class EliminaOrdineTest {

    private EliminaOrdine servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setUp() {
        servlet = new EliminaOrdine();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);

        when(request.getRequestDispatcher("gestisci-ordiniByUtente")).thenReturn(dispatcher);
    }

    /**
     * Test successful order deletion.
     * Scenario: Valid order ID is provided and order is deleted successfully
     */
    @Test
    void testDoGet_SuccessfulOrderDeletion() throws ServletException, IOException {
        // Arrange
        String ordineID = "ORD001";
        String utenteScelto = "user@example.com";

        when(request.getParameter("idOrdine")).thenReturn(ordineID);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteOrdine(ordineID);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            OrdineDAO mockDAO = mockedConstruction.constructed().get(0);
            verify(mockDAO).deleteOrdine(ordineID);
            verify(request).setAttribute("utenteScelto", utenteScelto);
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test request forwarding after deletion.
     * Scenario: After deleting an order, request is forwarded to the correct dispatcher
     */
    @Test
    void testDoGet_RequestForwardedCorrectly() throws ServletException, IOException {
        // Arrange
        String ordineID = "ORD002";
        String utenteScelto = "admin@example.com";

        when(request.getParameter("idOrdine")).thenReturn(ordineID);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteOrdine(ordineID);
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
        String ordineID = "ORD003";
        String utenteScelto = "newuser@example.com";

        when(request.getParameter("idOrdine")).thenReturn(ordineID);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteOrdine(ordineID);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute("utenteScelto", utenteScelto);
        }
    }

    /**
     * Test deleteOrdine is called with correct order ID.
     * Scenario: Verify that the correct order ID parameter is passed to deleteOrdine
     */
    @Test
    void testDoGet_DeleteOrdineCalledWithCorrectID() throws ServletException, IOException {
        // Arrange
        String ordineID = "ORD-2025-12345";
        String utenteScelto = "user@example.com";

        when(request.getParameter("idOrdine")).thenReturn(ordineID);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteOrdine(ordineID);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            OrdineDAO mockDAO = mockedConstruction.constructed().get(0);
            verify(mockDAO).deleteOrdine(ordineID);
        }
    }

    /**
     * Test deletion of multiple orders sequentially.
     * Scenario: Multiple different order IDs are deleted in sequence
     */
    @Test
    void testDoGet_MultipleDeletions() throws ServletException, IOException {
        String[] ordineIDs = {"ORD100", "ORD101", "ORD102"};

        for (String ordineID : ordineIDs) {
            // Reset mocks for each iteration
            reset(request, dispatcher);
            when(request.getRequestDispatcher("gestisci-ordiniByUtente")).thenReturn(dispatcher);

            String utenteScelto = "user@example.com";

            when(request.getParameter("idOrdine")).thenReturn(ordineID);
            when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

            try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
                doNothing().when(mock).deleteOrdine(ordineID);
            })) {
                // Act
                servlet.doGet(request, response);

                // Assert
                OrdineDAO mockDAO = mockedConstruction.constructed().get(0);
                verify(mockDAO).deleteOrdine(ordineID);
                verify(request).setAttribute("utenteScelto", utenteScelto);
            }
        }
    }

    /**
     * Test with special characters in order ID.
     * Scenario: Order ID contains special characters or hyphens
     */
    @Test
    void testDoGet_SpecialCharactersInOrderID() throws ServletException, IOException {
        // Arrange
        String ordineID = "ORD-2025-001-ABC";
        String utenteScelto = "user+admin@example.com";

        when(request.getParameter("idOrdine")).thenReturn(ordineID);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteOrdine(ordineID);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            OrdineDAO mockDAO = mockedConstruction.constructed().get(0);
            verify(mockDAO).deleteOrdine(ordineID);
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test operation sequence.
     * Scenario: Verify correct sequence of operations (delete, setAttribute, forward)
     */
    @Test
    void testDoGet_CorrectOperationSequence() throws ServletException, IOException {
        // Arrange
        String ordineID = "ORD004";
        String utenteScelto = "sequence@example.com";

        when(request.getParameter("idOrdine")).thenReturn(ordineID);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteOrdine(ordineID);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            OrdineDAO mockDAO = mockedConstruction.constructed().get(0);
            
            // Verify deleteOrdine is called
            verify(mockDAO, times(1)).deleteOrdine(ordineID);
            
            // Verify setAttribute is called
            verify(request).setAttribute("utenteScelto", utenteScelto);
            
            // Verify forward is called
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test with null order ID parameter.
     * Scenario: When ordineID parameter is null
     */
    @Test
    void testDoGet_NullOrdineIDParameter() throws ServletException, IOException {
        // Arrange
        String utenteScelto = "user@example.com";

        when(request.getParameter("idOrdine")).thenReturn(null);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteOrdine(null);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            OrdineDAO mockDAO = mockedConstruction.constructed().get(0);
            verify(mockDAO).deleteOrdine(null);
            verify(request).setAttribute("utenteScelto", utenteScelto);
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test with null utenteScelto parameter.
     * Scenario: When utenteScelto parameter is null
     */
    @Test
    void testDoGet_NullUtenteSceltoParameter() throws ServletException, IOException {
        // Arrange
        String ordineID = "ORD005";

        when(request.getParameter("idOrdine")).thenReturn(ordineID);
        when(request.getParameter("utenteScelto")).thenReturn(null);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteOrdine(ordineID);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            OrdineDAO mockDAO = mockedConstruction.constructed().get(0);
            verify(mockDAO).deleteOrdine(ordineID);
            verify(request).setAttribute("utenteScelto", null);
            verify(dispatcher).forward(request, response);
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
        String utenteScelto = "";

        when(request.getParameter("idOrdine")).thenReturn(ordineID);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteOrdine(ordineID);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            OrdineDAO mockDAO = mockedConstruction.constructed().get(0);
            verify(mockDAO).deleteOrdine(ordineID);
            verify(request).setAttribute("utenteScelto", utenteScelto);
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test with numeric order ID.
     * Scenario: Order ID containing only numbers
     */
    @Test
    void testDoGet_NumericOrdineID() throws ServletException, IOException {
        // Arrange
        String ordineID = "12345678";
        String utenteScelto = "user@example.com";

        when(request.getParameter("idOrdine")).thenReturn(ordineID);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteOrdine(ordineID);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            OrdineDAO mockDAO = mockedConstruction.constructed().get(0);
            verify(mockDAO).deleteOrdine(ordineID);
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test with long order ID value.
     * Scenario: Order ID with maximum length or very long string
     */
    @Test
    void testDoGet_LongOrdineIDValue() throws ServletException, IOException {
        // Arrange
        String ordineID = "ORD" + "0".repeat(100);
        String utenteScelto = "user@example.com";

        when(request.getParameter("idOrdine")).thenReturn(ordineID);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteOrdine(ordineID);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            OrdineDAO mockDAO = mockedConstruction.constructed().get(0);
            verify(mockDAO).deleteOrdine(ordineID);
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test DAODeleteOrdine is called exactly once.
     * Scenario: Verify that deleteOrdine is called exactly once per servlet request
     */
    @Test
    void testDoGet_DeleteOrdineCalledExactlyOnce() throws ServletException, IOException {
        // Arrange
        String ordineID = "ORD006";
        String utenteScelto = "user@example.com";

        when(request.getParameter("idOrdine")).thenReturn(ordineID);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteOrdine(ordineID);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            OrdineDAO mockDAO = mockedConstruction.constructed().get(0);
            verify(mockDAO, times(1)).deleteOrdine(ordineID);
        }
    }

    /**
     * Test deletion with complex order ID format.
     * Scenario: Order ID with mixed case and special characters
     */
    @Test
    void testDoGet_ComplexOrdineIDFormat() throws ServletException, IOException {
        // Arrange
        String ordineID = "ORD_2025_ABC-123-XYZ";
        String utenteScelto = "admin@example.com";

        when(request.getParameter("idOrdine")).thenReturn(ordineID);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteOrdine(ordineID);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            OrdineDAO mockDAO = mockedConstruction.constructed().get(0);
            verify(mockDAO).deleteOrdine(ordineID);
            verify(request).setAttribute("utenteScelto", utenteScelto);
        }
    }

    /**
     * Test correct request dispatcher path.
     * Scenario: Verify that the dispatcher is requested with exact path
     */
    @Test
    void testDoGet_CorrectDispatcherPath() throws ServletException, IOException {
        // Arrange
        String ordineID = "ORD007";
        String utenteScelto = "user@example.com";

        when(request.getParameter("idOrdine")).thenReturn(ordineID);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteOrdine(ordineID);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request, times(1)).getRequestDispatcher("gestisci-ordiniByUtente");
        }
    }

    /**
     * Test with whitespace in parameters.
     * Scenario: Parameters with leading/trailing whitespace
     */
    @Test
    void testDoGet_ParametersWithWhitespace() throws ServletException, IOException {
        // Arrange
        String ordineID = "  ORD008  ";
        String utenteScelto = "  user@example.com  ";

        when(request.getParameter("idOrdine")).thenReturn(ordineID);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteOrdine(ordineID);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            OrdineDAO mockDAO = mockedConstruction.constructed().get(0);
            verify(mockDAO).deleteOrdine(ordineID);
            verify(request).setAttribute("utenteScelto", utenteScelto);
        }
    }

    /**
     * Test deletion of order with special characters in user email.
     * Scenario: Verify correct attribute setting with special characters
     */
    @Test
    void testDoGet_SpecialCharactersInUserEmail() throws ServletException, IOException {
        // Arrange
        String ordineID = "ORD009";
        String utenteScelto = "user.name+tag@sub.example.com";

        when(request.getParameter("idOrdine")).thenReturn(ordineID);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteOrdine(ordineID);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute("utenteScelto", utenteScelto);
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test dispatcher forward is called after all operations.
     * Scenario: Forward is invoked at the end of processing
     */
    @Test
    void testDoGet_ForwardCalledAfterOperations() throws ServletException, IOException {
        // Arrange
        String ordineID = "ORD010";
        String utenteScelto = "user@example.com";

        when(request.getParameter("idOrdine")).thenReturn(ordineID);
        when(request.getParameter("utenteScelto")).thenReturn(utenteScelto);

        try (MockedConstruction<OrdineDAO> mockedConstruction = mockConstruction(OrdineDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteOrdine(ordineID);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            OrdineDAO mockDAO = mockedConstruction.constructed().get(0);
            
            // Both operations should be called
            verify(mockDAO).deleteOrdine(ordineID);
            verify(request).setAttribute("utenteScelto", utenteScelto);
            verify(dispatcher).forward(request, response);
        }
    }
}
