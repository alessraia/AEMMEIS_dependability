package controller.admin.gestisciSedi;

import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.Libro;
import model.libroService.Sede;
import model.libroService.SedeDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import static org.mockito.ArgumentMatchers.anyInt;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.*;
import org.mockito.InOrder;

/**
 * Unit tests for ModificaSedeServlet
 * Tests the servlet's ability to remove books from store locations (sedi) and handle
 * the removal process with proper redirection.
 */
class ModificaSedeServletTest {

    private ModificaSedeServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;

    @BeforeEach
    void setUp() {
        servlet = new ModificaSedeServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
    }

    /**
     * Test successful removal of book from sede
     * Scenario: Valid ISBN and sede ID are provided and book is removed
     */
    @Test
    void testDoGet_SuccessfulBookRemoval() throws IOException {
        // Arrange
        when(request.getParameter("isbn")).thenReturn("ISBN-001");
        when(request.getParameter("idSede")).thenReturn("1");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).removeLibroSede(1, "ISBN-001");
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify redirect occurs
            verify(response).sendRedirect("gestisci-sedi");
        }
    }

    /**
     * Test removal of multiple books from different sedes
     * Scenario: Different ISBN and sede ID combinations
     */
    @Test
    void testDoGet_RemovalWithDifferentIds() throws IOException {
        // Arrange
        when(request.getParameter("isbn")).thenReturn("ISBN-XYZ");
        when(request.getParameter("idSede")).thenReturn("42");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).removeLibroSede(42, "ISBN-XYZ");
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify removeLibroSede called with correct parameters
            verify(mockedConstruction.constructed().get(0)).removeLibroSede(42, "ISBN-XYZ");
        }
    }

    /**
     * Test correct parameter parsing
     * Scenario: String parameters are correctly converted to int for sede ID
     */
    @Test
    void testDoGet_CorrectParameterParsing() throws IOException {
        // Arrange
        String isbnStr = "ISBN-TEST";
        String sedeIdStr = "99";
        int expectedSedeId = 99;
        when(request.getParameter("isbn")).thenReturn(isbnStr);
        when(request.getParameter("idSede")).thenReturn(sedeIdStr);

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).removeLibroSede(expectedSedeId, isbnStr);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify exact parameters are used
            verify(mockedConstruction.constructed().get(0)).removeLibroSede(expectedSedeId, isbnStr);
        }
    }

    /**
     * Test removal with standard ISBN format
     * Scenario: Standard ISBN-13 format is handled correctly
     */
    @Test
    void testDoGet_StandardIsbnFormat() throws IOException {
        // Arrange
        when(request.getParameter("isbn")).thenReturn("978-3-16-148410-0");
        when(request.getParameter("idSede")).thenReturn("5");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).removeLibroSede(5, "978-3-16-148410-0");
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(mockedConstruction.constructed().get(0)).removeLibroSede(5, "978-3-16-148410-0");
        }
    }

    /**
     * Test removal with minimum valid sede ID
     * Scenario: Sede ID = 1
     */
    @Test
    void testDoGet_MinimumSedeId() throws IOException {
        // Arrange
        when(request.getParameter("isbn")).thenReturn("ISBN-001");
        when(request.getParameter("idSede")).thenReturn("1");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).removeLibroSede(1, "ISBN-001");
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(mockedConstruction.constructed().get(0)).removeLibroSede(1, "ISBN-001");
        }
    }

    /**
     * Test removal with large sede ID
     * Scenario: Large sede ID number
     */
    @Test
    void testDoGet_LargeSedeId() throws IOException {
        // Arrange
        when(request.getParameter("isbn")).thenReturn("ISBN-001");
        when(request.getParameter("idSede")).thenReturn("999999");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).removeLibroSede(999999, "ISBN-001");
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(mockedConstruction.constructed().get(0)).removeLibroSede(999999, "ISBN-001");
        }
    }

    /**
     * Test exception propagation from database
     * Scenario: RuntimeException during removeLibroSede is propagated
     */
    @Test
    void testDoGet_ExceptionPropagation() throws IOException {
        // Arrange
        when(request.getParameter("isbn")).thenReturn("ISBN-001");
        when(request.getParameter("idSede")).thenReturn("1");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doThrow(new RuntimeException("DELETE error.")).when(mock).removeLibroSede(anyInt(), anyString());
        })) {
            // Act & Assert
            try {
                servlet.doGet(request, response);
            } catch (RuntimeException e) {
                assert e.getMessage().contains("DELETE error");
            }
        }
    }

    /**
     * Test redirect occurs after successful removal
     * Scenario: Redirect URL should be set after removal completes
     */
    @Test
    void testDoGet_RedirectAfterRemoval() throws IOException {
        // Arrange
        when(request.getParameter("isbn")).thenReturn("ISBN-001");
        when(request.getParameter("idSede")).thenReturn("3");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).removeLibroSede(3, "ISBN-001");
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify redirect is called exactly once
            verify(response, times(1)).sendRedirect("gestisci-sedi");
        }
    }

    /**
     * Test correct redirect URL
     * Scenario: Verify exact redirect path
     */
    @Test
    void testDoGet_CorrectRedirectUrl() throws IOException {
        // Arrange
        when(request.getParameter("isbn")).thenReturn("ISBN-001");
        when(request.getParameter("idSede")).thenReturn("7");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).removeLibroSede(7, "ISBN-001");
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify exact redirect URL
            verify(response).sendRedirect("gestisci-sedi");
        }
    }

    /**
     * Test SedeDAO instantiation
     * Scenario: Verify SedeDAO is created exactly once per request
     */
    @Test
    void testDoGet_SedeDAOInstantiated() throws IOException {
        // Arrange
        when(request.getParameter("isbn")).thenReturn("ISBN-001");
        when(request.getParameter("idSede")).thenReturn("1");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).removeLibroSede(1, "ISBN-001");
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify SedeDAO constructor called exactly once
            assert mockedConstruction.constructed().size() == 1;
        }
    }

    /**
     * Test removeLibroSede is called exactly once
     * Scenario: Verify the removal method is called once per request
     */
    @Test
    void testDoGet_RemoveLibroSedeCalledOnce() throws IOException {
        // Arrange
        when(request.getParameter("isbn")).thenReturn("ISBN-001");
        when(request.getParameter("idSede")).thenReturn("2");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).removeLibroSede(2, "ISBN-001");
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify removeLibroSede called exactly once
            verify(mockedConstruction.constructed().get(0), times(1)).removeLibroSede(2, "ISBN-001");
        }
    }

    /**
     * Test with numeric ISBN
     * Scenario: ISBN contains only digits
     */
    @Test
    void testDoGet_NumericIsbn() throws IOException {
        // Arrange
        when(request.getParameter("isbn")).thenReturn("9780743273565");
        when(request.getParameter("idSede")).thenReturn("4");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).removeLibroSede(4, "9780743273565");
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(mockedConstruction.constructed().get(0)).removeLibroSede(4, "9780743273565");
        }
    }

    /**
     * Test with ISBN containing hyphens
     * Scenario: ISBN with hyphen separators
     */
    @Test
    void testDoGet_IsbnWithHyphens() throws IOException {
        // Arrange
        when(request.getParameter("isbn")).thenReturn("0-7432-7356-5");
        when(request.getParameter("idSede")).thenReturn("6");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).removeLibroSede(6, "0-7432-7356-5");
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(mockedConstruction.constructed().get(0)).removeLibroSede(6, "0-7432-7356-5");
        }
    }

    /**
     * Test multiple sequential removals
     * Scenario: Multiple removal requests in sequence
     */
    @Test
    void testDoGet_MultipleSequentialRemovals() throws IOException {
        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).removeLibroSede(anyInt(), anyString());
        })) {
            // Act: Perform three removals
            for (int i = 1; i <= 3; i++) {
                when(request.getParameter("isbn")).thenReturn("ISBN-" + i);
                when(request.getParameter("idSede")).thenReturn(String.valueOf(i));
                servlet.doGet(request, response);
            }

            // Assert: Each removal should result in redirect
            verify(response, times(3)).sendRedirect("gestisci-sedi");
        }
    }

    /**
     * Test with zero sede ID
     * Scenario: Edge case with sede ID = 0
     */
    @Test
    void testDoGet_ZeroSedeId() throws IOException {
        // Arrange
        when(request.getParameter("isbn")).thenReturn("ISBN-001");
        when(request.getParameter("idSede")).thenReturn("0");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).removeLibroSede(0, "ISBN-001");
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(mockedConstruction.constructed().get(0)).removeLibroSede(0, "ISBN-001");
        }
    }

    /**
     * Test with negative sede ID
     * Scenario: Edge case with negative sede ID
     */
    @Test
    void testDoGet_NegativeSedeId() throws IOException {
        // Arrange
        when(request.getParameter("isbn")).thenReturn("ISBN-001");
        when(request.getParameter("idSede")).thenReturn("-5");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).removeLibroSede(-5, "ISBN-001");
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(mockedConstruction.constructed().get(0)).removeLibroSede(-5, "ISBN-001");
        }
    }

    /**
     * Test ISBN parameter is passed as string
     * Scenario: ISBN should be passed without modification
     */
    @Test
    void testDoGet_IsbnStringPreservation() throws IOException {
        // Arrange
        String testIsbn = "ISBN@#$%^&*";
        when(request.getParameter("isbn")).thenReturn(testIsbn);
        when(request.getParameter("idSede")).thenReturn("8");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).removeLibroSede(8, testIsbn);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: ISBN should be passed exactly as received
            verify(mockedConstruction.constructed().get(0)).removeLibroSede(8, testIsbn);
        }
    }

    /**
     * Test with empty ISBN string
     * Scenario: Edge case with empty ISBN
     */
    @Test
    void testDoGet_EmptyIsbn() throws IOException {
        // Arrange
        when(request.getParameter("isbn")).thenReturn("");
        when(request.getParameter("idSede")).thenReturn("9");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).removeLibroSede(9, "");
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(mockedConstruction.constructed().get(0)).removeLibroSede(9, "");
        }
    }

    /**
     * Test removal with very long ISBN string
     * Scenario: ISBN with many characters
     */
    @Test
    void testDoGet_LongIsbnString() throws IOException {
        // Arrange
        String longIsbn = "ISBN-" + "X".repeat(100);
        when(request.getParameter("isbn")).thenReturn(longIsbn);
        when(request.getParameter("idSede")).thenReturn("10");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).removeLibroSede(10, longIsbn);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(mockedConstruction.constructed().get(0)).removeLibroSede(10, longIsbn);
        }
    }

    /**
     * Test removal called before redirect
     * Scenario: Verify removeLibroSede is called before sendRedirect
     */
    @Test
    void testDoGet_RemovalBeforeRedirect() throws IOException {
        // Arrange
        when(request.getParameter("isbn")).thenReturn("ISBN-001");
        when(request.getParameter("idSede")).thenReturn("11");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).removeLibroSede(11, "ISBN-001");
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify order - removeLibroSede called before redirect
            InOrder inOrder = inOrder(mockedConstruction.constructed().get(0), response);
            inOrder.verify(mockedConstruction.constructed().get(0)).removeLibroSede(11, "ISBN-001");
            inOrder.verify(response).sendRedirect("gestisci-sedi");
        }
    }

    /**
     * Test no request dispatcher usage
     * Scenario: Verify this is a redirect servlet, not a forward servlet
     */
    @Test
    void testDoGet_NoRequestDispatcher() throws IOException {
        // Arrange
        when(request.getParameter("isbn")).thenReturn("ISBN-001");
        when(request.getParameter("idSede")).thenReturn("12");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).removeLibroSede(12, "ISBN-001");
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: getRequestDispatcher should not be called
            verify(request, never()).getRequestDispatcher(anyString());
        }
    }

    /**
     * Test with alphanumeric ISBN
     * Scenario: ISBN with mixed alphanumeric characters
     */
    @Test
    void testDoGet_AlphanumericIsbn() throws IOException {
        // Arrange
        when(request.getParameter("isbn")).thenReturn("ISBN123ABC456XYZ");
        when(request.getParameter("idSede")).thenReturn("13");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).removeLibroSede(13, "ISBN123ABC456XYZ");
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(mockedConstruction.constructed().get(0)).removeLibroSede(13, "ISBN123ABC456XYZ");
        }
    }
}
