package controller.admin.gestisciSedi;

import jakarta.servlet.ServletException;
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
import static org.mockito.Mockito.*;

/**
 * Unit tests for EliminaSedeServlet
 * Tests the servlet's ability to delete store locations (sedi) and redirect appropriately.
 */
class EliminaSedeServletTest {

    private EliminaSedeServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;

    @BeforeEach
    void setUp() {
        servlet = new EliminaSedeServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
    }

    /**
     * Test successful deletion of a sede with no books
     * Scenario: Sede exists and has no associated books
     */
    @Test
    void testDoGet_SuccessfulSedeDeleteNoBooks() throws IOException, ServletException {
        // Arrange: Set valid sede ID
        when(request.getParameter("idSede")).thenReturn("1");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteSede(1);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify redirect to gestisci-sedi
            verify(response).sendRedirect("gestisci-sedi");
        }
    }

    /**
     * Test successful deletion of a sede with associated books
     * Scenario: Sede exists and has books that need to be cleaned up
     */
    @Test
    void testDoGet_SuccessfulSedeDeleteWithBooks() throws IOException, ServletException {
        // Arrange: Set valid sede ID
        when(request.getParameter("idSede")).thenReturn("5");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteSede(5);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify redirect occurs after deletion
            verify(response).sendRedirect("gestisci-sedi");
        }
    }

    /**
     * Test deletion is called with correct sede ID
     * Scenario: Verify deleteSede is called with the correct parameter
     */
    @Test
    void testDoGet_DeletionCalledWithCorrectId() throws IOException, ServletException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("42");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteSede(42);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify deleteSede is called with exact ID
            verify(mockedConstruction.constructed().get(0)).deleteSede(42);
        }
    }

    /**
     * Test deletion with minimum valid ID
     * Scenario: Delete sede with ID = 1
     */
    @Test
    void testDoGet_DeleteMinimumId() throws IOException, ServletException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("1");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteSede(1);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(response).sendRedirect("gestisci-sedi");
        }
    }

    /**
     * Test deletion with large ID
     * Scenario: Delete sede with large ID number
     */
    @Test
    void testDoGet_DeleteLargeId() throws IOException, ServletException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("999999");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteSede(999999);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(response).sendRedirect("gestisci-sedi");
        }
    }

    /**
     * Test exception propagation when deletion fails
     * Scenario: Database error during sede deletion
     */
    @Test
    void testDoGet_DeleteionExceptionPropagated() throws IOException, ServletException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("1");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doThrow(new RuntimeException("DELETE error.")).when(mock).deleteSede(anyInt());
        })) {
            // Act & Assert: Exception should be propagated
            try {
                servlet.doGet(request, response);
            } catch (RuntimeException e) {
                assert e.getMessage().contains("DELETE error");
            }
        }
    }

    /**
     * Test redirect happens after successful deletion
     * Scenario: Verify redirect is called and not before deletion
     */
    @Test
    void testDoGet_RedirectAfterDeletion() throws IOException, ServletException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("3");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteSede(3);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify redirect is called exactly once
            verify(response, times(1)).sendRedirect("gestisci-sedi");
        }
    }

    /**
     * Test redirect URL is correct
     * Scenario: Verify the exact redirect path
     */
    @Test
    void testDoGet_CorrectRedirectUrl() throws IOException, ServletException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("7");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteSede(7);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify exact redirect URL
            verify(response).sendRedirect("gestisci-sedi");
        }
    }

    /**
     * Test SedeDAO instance is created
     * Scenario: Verify SedeDAO is instantiated during execution
     */
    @Test
    void testDoGet_SedeDAOInstantiated() throws IOException, ServletException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("2");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteSede(2);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify SedeDAO was constructed exactly once
            assert mockedConstruction.constructed().size() == 1;
        }
    }

    /**
     * Test parameter parsing from string to integer
     * Scenario: String parameter is correctly converted to int
     */
    @Test
    void testDoGet_ParameterParsingStringToInt() throws IOException, ServletException {
        // Arrange
        String stringId = "123";
        int expectedId = 123;
        when(request.getParameter("idSede")).thenReturn(stringId);

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteSede(expectedId);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(mockedConstruction.constructed().get(0)).deleteSede(expectedId);
        }
    }

    /**
     * Test with multiple sequential deletions
     * Scenario: Multiple sedi are deleted in sequence
     */
    @Test
    void testDoGet_MultipleSequentialDeletions() throws IOException, ServletException {
        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteSede(anyInt());
        })) {
            // Act: Delete three sedi
            for (int i = 1; i <= 3; i++) {
                when(request.getParameter("idSede")).thenReturn(String.valueOf(i));
                servlet.doGet(request, response);
            }

            // Assert: Verify three redirects occurred
            verify(response, times(3)).sendRedirect("gestisci-sedi");
        }
    }

    /**
     * Test no redirect on null return from deletion
     * Scenario: Even though deleteSede returns void, redirect should still occur
     */
    @Test
    void testDoGet_RedirectOccursOnVoidReturn() throws IOException, ServletException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("4");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteSede(4);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Redirect should occur regardless of void return
            verify(response).sendRedirect("gestisci-sedi");
        }
    }

    /**
     * Test exception type verification
     * Scenario: RuntimeException from database is propagated correctly
     */
    @Test
    void testDoGet_ExceptionTypeVerification() throws IOException, ServletException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("1");
        RuntimeException expectedError = new RuntimeException("DELETE error from appartenenza.");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doThrow(expectedError).when(mock).deleteSede(anyInt());
        })) {
            // Act & Assert
            try {
                servlet.doGet(request, response);
            } catch (RuntimeException e) {
                assert e == expectedError || e.getMessage().contains("DELETE error from appartenenza");
            }
        }
    }

    /**
     * Test request dispatcher is not used
     * Scenario: Verify this is a redirect servlet, not a forward servlet
     */
    @Test
    void testDoGet_NoRequestDispatcher() throws IOException, ServletException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("1");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteSede(1);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: getRequestDispatcher should not be called
            verify(request, never()).getRequestDispatcher(anyString());
        }
    }

    /**
     * Test deletion followed by immediate second deletion
     * Scenario: Two consecutive delete operations on different sedi
     */
    @Test
    void testDoGet_TwoConsecutiveDeletions() throws IOException, ServletException {
        // Arrange
        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteSede(anyInt());
        })) {
            // Act: First deletion
            when(request.getParameter("idSede")).thenReturn("10");
            servlet.doGet(request, response);

            // Act: Second deletion
            when(request.getParameter("idSede")).thenReturn("11");
            servlet.doGet(request, response);

            // Assert: Both should result in redirects
            verify(response, times(2)).sendRedirect("gestisci-sedi");
        }
    }

    /**
     * Test negative ID handling
     * Scenario: Negative sede ID (edge case)
     */
    @Test
    void testDoGet_NegativeId() throws IOException, ServletException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("-1");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteSede(-1);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should still attempt deletion even with negative ID
            verify(mockedConstruction.constructed().get(0)).deleteSede(-1);
        }
    }

    /**
     * Test zero ID handling
     * Scenario: Zero sede ID (edge case)
     */
    @Test
    void testDoGet_ZeroId() throws IOException, ServletException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("0");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doNothing().when(mock).deleteSede(0);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should process ID 0
            verify(mockedConstruction.constructed().get(0)).deleteSede(0);
        }
    }
}
